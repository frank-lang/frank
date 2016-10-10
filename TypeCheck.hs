-- Inspired by Adam Gundry et al.'s treatment of type inference in
-- context. See Gundry's thesis (most closely aligned) or the paper ``Type
-- inference in Context'' for more details.
{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
module TypeCheck where

import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import BwdFwd
import Syntax
import FreshNames
import TypeCheckCommon
import Unification

-- Only to be applied to identifiers representing rigid or flexible type
-- variables.
trimTVar :: Id -> Id
trimTVar = takeWhile (/= '$')

freshFTVar :: Id -> Contextual Id
freshFTVar x = do n <- fresh
                  let s = trimTVar x ++ "$f" ++ (show n)
                  modify (:< FlexTVar s Hole)
                  return s

find :: Operator -> Contextual (VType Desugared)
find (MkCmdId x) =
  do amb <- getAmbient
     (itf, qs, ts, y) <- getCmd x
     case lkpItf itf amb of
       Nothing -> throwError $ "command " ++ (show x) ++
                  " belonging to interface " ++ (show itf) ++
                  " not permitted by ambient ability"
       Just ps ->
         do addMark
            qs' <- mapM makeFlexible qs
            ts' <- mapM makeFlexible ts
            y' <- makeFlexible y
            mapM (uncurry unify) (zip ps qs')
            return $ MkSCTy $
              MkCType (map (\x -> MkPort MkIdAdj x) ts') (MkPeg amb y')
find x = getContext >>= find'
  where find' BEmp = throwError $ show x ++ " not in scope"
        find' (es :< TermVar y ty) | x == y = return ty
        find' (es :< _) = find' es

-- Run a contextual computation with an additonal term variable in scope
inScope :: Operator -> VType Desugared -> Contextual a -> Contextual a
inScope x ty m = do modify (:< TermVar x ty)
                    a <- m
                    modify dropVar
                    return a
  where dropVar :: Context -> Context
        dropVar BEmp = error "Invariant violation"
        dropVar (es :< TermVar y _) | x == y = es
        dropVar (es :< e) = dropVar es :< e

-- Run a contextual computation in a modified ambient environment
inAmbient :: Adj Desugared -> Contextual a -> Contextual a
inAmbient adj m = do amb <- getAmbient
                     putAmbient (plus amb adj)
                     a <- m
                     putAmbient amb
                     return a

lkpItf :: Id -> Ab Desugared -> Maybe [VType Desugared]
lkpItf itf MkEmpAb = Nothing
lkpItf itf MkOpenAb = Nothing
lkpItf itf (MkAbPlus ab id xs)
  | itf == id = Just xs
  | otherwise = lkpItf itf ab

-- Only instantiate polytypic operators
instantiate :: Operator -> VType Desugared -> Contextual (VType Desugared)
instantiate (MkPoly _) ty = do addMark
                               ty' <- makeFlexible ty
                               ty'' <- substOpenAb ty'
                               return ty''
instantiate _ ty = return ty

-- Main typechecking function
checkProg :: Prog Desugared -> Contextual ()
checkProg p = do MkProg xs <- initContextual p
                 return ()

checkTopTm :: TopTm Desugared -> Contextual ()
checkTopTm (MkDefTm def) = checkMHDef def
checkTopTm _ = return ()

checkMHDef :: MHDef Desugared -> Contextual ()
checkMHDef (MkDef id ty@(MkCType ps q) cs) =
  do modify (:< TermVar (MkPoly id) (MkSCTy ty))
     mapM_ (\cls -> checkCls cls ps q) cs


-- Functions below implement the typing rules described in the paper.
inferUse :: Use Desugared -> Contextual (VType Desugared)
inferUse (MkOp x) = find x >>= (instantiate x)
inferUse (MkApp f xs) = do ty <- find f >>= (instantiate f)
                           case ty of
                             MkSCTy (MkCType ps q) -> do checkArgs ps xs
                                                         returnResult q
                             _ -> throwError $
                                  "application:expected suspended computation"
  where checkArgs :: [Port Desugared] -> [Tm Desugared] -> Contextual ()
        checkArgs ps xs = mapM_ (uncurry checkArg) (zip ps xs)

        checkArg :: Port Desugared -> Tm Desugared -> Contextual ()
        checkArg (MkPort adj ty) tm = inAmbient adj (checkTm tm ty)

        returnResult :: Peg Desugared -> Contextual (VType Desugared)
        returnResult (MkPeg ab ty) =
          do amb <- getAmbient
             let xs = sortUniq $ abToList ab
                 ys = sortUniq $ abToList amb
             if xs == ys then return ty
             else throwError $ "peg does not match ambient ability"

checkTm :: Tm Desugared -> VType Desugared -> Contextual ()
checkTm (MkSC sc) (MkSCTy cty) = checkSComp sc cty
checkTm MkLet _ = return ()
checkTm (MkStr _) MkStringTy = return ()
checkTm (MkInt _) MkIntTy = return ()
checkTm (MkChar _) MkCharTy = return ()
checkTm (MkTmSeq tm1 tm2) ty = do ftvar <- freshFTVar "seq"
                                  checkTm tm1 (MkFTVar ftvar)
                                  checkTm tm2 ty
checkTm (MkUse u) t = do s <- inferUse u
                         unify t s
checkTm (MkDCon (MkDataCon k xs)) (MkDTTy dt ab ps) =
  do (qs, ts) <- getCtr k dt
     addMark
     qs' <- mapM makeFlexible qs
     ts' <- mapM makeFlexible ts
     mapM_ (uncurry unify) (zip ps qs')
     mapM_ (uncurry checkTm) (zip xs ts')
checkTm tm ty = throwError $
                "failed to term " ++ show tm ++ " against type " ++ show ty

checkSComp :: SComp Desugared -> CType Desugared -> Contextual ()
checkSComp (MkSComp xs) (MkCType ps q) = mapM_ (\cls -> checkCls cls ps q) xs

checkCls :: Clause Desugared -> [Port Desugared] -> Peg Desugared ->
            Contextual ()
checkCls (MkCls pats tm) ports (MkPeg ab ty)
  | length pats == length ports =
    do putAmbient ab
       bs <- fmap concat $ mapM (uncurry checkPat) (zip pats ports)
       -- Bring any bindings in to scope for checking the term then purge the
       -- marks (and suffixes) in the context created for this clause.
       case null bs of
         True -> do checkTm tm ty
                    purgeMarks
         False -> do foldl1 (.) (map (uncurry inScope) bs) $ checkTm tm ty
                     purgeMarks
  | otherwise = throwError "number of patterns not equal to number of ports"

checkPat :: Pattern -> Port Desugared -> Contextual [TermBinding]
checkPat (MkVPat vp) (MkPort _ ty) = checkVPat vp ty
checkPat (MkCmdPat cmd xs g) (MkPort adj ty) =
  do (itf, qs, ts, y) <- getCmd cmd
     case lkpItf itf (plus MkEmpAb adj) of
       Nothing -> throwError $
                  "command " ++ cmd ++ " not found in adjustment " ++
                  (show adj)
       Just ps -> do addMark -- localise the following type variables
                     qs' <- mapM makeFlexible qs
                     ts' <- mapM makeFlexible ts
                     y' <- makeFlexible y
                     mapM (uncurry unify) (zip ps qs')
                     bs <- fmap concat $ mapM (uncurry checkVPat) (zip xs ts')
                     kty <- contType y' adj ty
                     return ((MkMono g,kty) : bs)
checkPat (MkThkPat x) (MkPort adj ty) =
  do amb <- getAmbient
     return $ [(MkMono x, MkSCTy $ MkCType [] (MkPeg (plus amb adj) ty))]

contType :: VType Desugared -> Adj Desugared -> VType Desugared ->
            Contextual (VType Desugared)
contType x adj y =
  do amb <- getAmbient
     return $ MkSCTy $ MkCType [MkPort MkIdAdj x] (MkPeg (plus amb adj) y)

checkVPat :: ValuePat -> VType Desugared -> Contextual [TermBinding]
checkVPat (MkVarPat x) ty = return [(MkMono x, ty)]
checkVPat (MkDataPat k xs) (MkDTTy dt ab ps) =
  do (qs, ts) <- getCtr k dt
     addMark
     qs' <- mapM makeFlexible qs
     ts' <- mapM makeFlexible ts
     mapM_ (uncurry unify) (zip ps qs')
     bs <- fmap concat $ mapM (uncurry checkVPat) (zip xs ts')
     return bs
checkVPat (MkCharPat _) MkCharTy = return []
checkVPat (MkStrPat _) MkStringTy = return []
checkVPat (MkIntPat _) MkIntTy = return []
checkVPat _ _ = throwError "failed to match value pattern and type"

-- Replace rigid type variables with flexible ones
makeFlexible :: VType Desugared -> Contextual (VType Desugared)
makeFlexible (MkDTTy id ab xs) = MkDTTy <$> pure id <*>
                                 makeFlexibleAb ab <*> mapM makeFlexible xs
makeFlexible (MkSCTy cty) = MkSCTy <$> makeFlexibleCType cty
makeFlexible (MkRTVar x) = MkFTVar <$> (getContext >>= find')
  where find' BEmp = freshFTVar x
        find' (es :< FlexTVar y _) | trimTVar x == trimTVar y = return x
        find' (es :< Mark) = freshFTVar x
        find' (es :< _) = find' es

makeFlexible ty = return ty

makeFlexibleAb :: Ab Desugared -> Contextual (Ab Desugared)
makeFlexibleAb (MkAbPlus ab itf xs) = MkAbPlus <$>
                                      makeFlexibleAb ab <*>
                                      pure itf <*>
                                      mapM makeFlexible xs
makeFlexibleAb ab = return ab

makeFlexibleAdj :: Adj Desugared -> Contextual (Adj Desugared)
makeFlexibleAdj (MkAdjPlus adj itf xs) = MkAdjPlus <$>
                                         makeFlexibleAdj adj <*>
                                         pure itf <*>
                                         mapM makeFlexible xs

makeFlexibleCType :: CType Desugared -> Contextual (CType Desugared)
makeFlexibleCType (MkCType ps q) = MkCType <$>
                                   mapM makeFlexiblePort ps <*>
                                   makeFlexiblePeg q

makeFlexiblePeg :: Peg Desugared -> Contextual (Peg Desugared)
makeFlexiblePeg (MkPeg ab ty) = MkPeg <$>
                                makeFlexibleAb ab <*>
                                makeFlexible ty

makeFlexiblePort :: Port Desugared -> Contextual (Port Desugared)
makeFlexiblePort (MkPort adj ty) = MkPort <$>
                                   makeFlexibleAdj adj <*>
                                   makeFlexible ty

-- Substitute the ambient for the effect variable
substOpenAb :: VType Desugared -> Contextual (VType Desugared)
substOpenAb (MkDTTy id ab xs) = MkDTTy <$> pure id <*> substOpenAbAb ab <*>
                                mapM substOpenAb xs
substOpenAb (MkSCTy cty) = MkSCTy <$> substOpenAbCType cty
substOpenAb ty = return ty

substOpenAbAb :: Ab Desugared -> Contextual (Ab Desugared)
substOpenAbAb MkEmpAb = return MkEmpAb
substOpenAbAb MkOpenAb = getAmbient
substOpenAbAb (MkAbPlus ab itf xs) = do ab' <- substOpenAbAb ab
                                        xs' <- mapM substOpenAb xs
                                        return $ MkAbPlus ab' itf xs'

substOpenAbAdj :: Adj Desugared -> Contextual (Adj Desugared)
substOpenAbAdj MkIdAdj = return MkIdAdj
substOpenAbAdj (MkAdjPlus adj itf xs) = do adj' <- substOpenAbAdj adj
                                           xs' <- mapM substOpenAb xs
                                           return $ MkAdjPlus adj' itf xs'

substOpenAbCType :: CType Desugared -> Contextual (CType Desugared)
substOpenAbCType (MkCType ps q) =
  MkCType <$> mapM substOpenAbPort ps <*> substOpenAbPeg q

substOpenAbPeg :: Peg Desugared -> Contextual (Peg Desugared)
substOpenAbPeg (MkPeg ab ty) = MkPeg <$> substOpenAbAb ab <*>
                               substOpenAb ty

substOpenAbPort :: Port Desugared -> Contextual (Port Desugared)
substOpenAbPort (MkPort adj ty) = MkPort <$> substOpenAbAdj adj <*>
                                  substOpenAb ty

plus :: Ab Desugared -> Adj Desugared -> Ab Desugared
plus ab MkIdAdj = ab
plus ab (MkAdjPlus adj itf xs) = MkAbPlus (plus ab adj) itf xs
