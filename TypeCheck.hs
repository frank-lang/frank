-- Inspired by Adam Gundry et al.'s treatment of type inference in
-- context. See Gundry's thesis (most closely aligned) or the paper ``Type
-- inference in Context'' for more details.
{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
module TypeCheck where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import Data.List.Unique

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import Debug.Trace

import BwdFwd
import Syntax
import FreshNames
import TypeCheckCommon
import Unification

type EVMap a = M.Map Id (Ab a)

find :: Operator -> Contextual (VType Desugared)
find (MkCmdId x) =
  do amb <- getAmbient
     (itf, qs, ts, y) <- getCmd x
     mps <- lkpItf itf amb
     case mps of
       Nothing -> throwError $ "command " ++ x ++
                  " belonging to interface " ++ itf ++
                  " not permitted by ambient ability:" ++
                  (show $ ppAb amb)
       Just ps ->
         do addMark
            qs' <- mapM makeFlexibleTyArg qs
            ts' <- mapM makeFlexible ts
            y' <- makeFlexible y
            mapM (uncurry unifyTyArg) (zip ps qs')
            return $ MkSCTy $
              MkCType (map (\x -> MkPort idAdj x) ts') (MkPeg amb y')
find x = getContext >>= find'
  where find' BEmp = throwError $ "'" ++ getOpName x ++ "' not in scope"
        find' (es :< TermVar y ty) | x == y = return ty
        find' (es :< _) = find' es

-- Find the first non-flexible type definition for the specified identifier.
findFTVar :: Id -> Contextual (Maybe (VType Desugared))
findFTVar x = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (TyDefn ty)) | x == y = return $ Just ty
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

lkpItf :: Id -> Ab Desugared -> Contextual (Maybe [TyArg Desugared])
lkpItf itf (MkAb v m) =
  case M.lookup itf m of
    Nothing -> lkpItfInAbMod itf v
    Just xs -> return $ Just xs

lkpItfInAbMod :: Id -> AbMod Desugared -> Contextual (Maybe [TyArg Desugared])
lkpItfInAbMod itf (MkAbFVar x) = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (AbDefn ab)) | x == y = lkpItf itf ab
        find' (es :< _) = find' es
lkpItfInAbMod itf v = return Nothing

-- Only instantiate polytypic operators
instantiate :: Operator -> VType Desugared -> Contextual (VType Desugared)
instantiate (MkPoly _) ty = addMark >> makeFlexible ty
instantiate _ ty = return ty

-- TODO: change output of check to Maybe String?

-- infer the type of a use w.r.t. the given program
inferEvalUse :: Prog Desugared -> Use Desugared ->
                Either String (VType Desugared)
inferEvalUse p use = runExcept $ evalFreshMT $ evalStateT comp initTCState
  where comp = unCtx $ do _ <- initContextual p
                          inferUse use

-- Main typechecking function
check :: Prog Desugared -> Either String (Prog Desugared)
check p = runExcept $ evalFreshMT $ evalStateT (checkProg p) initTCState
  where
    checkProg p = unCtx $ do MkProg xs <- initContextual p
                             mapM checkTopTm xs
                             return $ MkProg xs

checkTopTm :: TopTm Desugared -> Contextual ()
checkTopTm (MkDefTm def) = checkMHDef def
checkTopTm _ = return ()

checkMHDef :: MHDef Desugared -> Contextual ()
checkMHDef (MkDef id ty@(MkCType ps q) cs) =
  do mapM_ (\cls -> checkCls cls ps q) cs

-- Functions below implement the typing rules described in the paper.
inferUse :: Use Desugared -> Contextual (VType Desugared)
inferUse (MkOp x) = find x >>= (instantiate x)
inferUse app@(MkApp f xs) =
  do ty <- inferUse f
     discriminate ty
  where appAbError :: String -> Contextual ()
        appAbError msg | inDebugMode = throwError (msg ++ " in " ++ show app)
        appAbError msg = throwError msg

        checkArgs :: [Port Desugared] -> [Tm Desugared] -> Contextual ()
        checkArgs ps xs = mapM_ (uncurry checkArg) (zip ps xs)

        checkArg :: Port Desugared -> Tm Desugared -> Contextual ()
        checkArg (MkPort adj ty) tm = inAmbient adj (checkTm tm ty)

        discriminate :: VType Desugared -> Contextual (VType Desugared)
        discriminate ty@(MkSCTy (MkCType ps (MkPeg ab ty'))) =
          do amb <- getAmbient
             catchError (unifyAb amb ab) appAbError
             checkArgs ps xs
             return ty'
        discriminate ty@(MkFTVar x) =
          do mty <- findFTVar x
             case mty of
               Nothing ->
                 -- TODO: check that this is correct
                 do addMark
                    amb <- getAmbient
                    ps <- mapM (\_ -> freshPort "X") xs
                    q@(MkPeg ab ty')  <- freshPegWithAb amb "Y"
                    unify ty (MkSCTy (MkCType ps q))
                    return ty'
                 -- errTy ty
               Just ty' -> discriminate ty'
        discriminate ty = errTy ty

        -- TODO: tidy.
        -- We don't need to report an error here, but rather generate
        -- appropriate fresh type variables as above.
        errTy ty = throwError $
                   "application (" ++ show (MkApp f xs) ++ 
                   "): expected suspended computation but got " ++
                   (show $ ppVType ty)

checkTm :: Tm Desugared -> VType Desugared -> Contextual ()
checkTm (MkSC sc) ty = checkSComp sc ty
checkTm (MkStr _) ty = unify desugaredStrTy ty
checkTm (MkInt _) ty = unify MkIntTy ty
checkTm (MkChar _) ty = unify MkCharTy ty
checkTm (MkTmSeq tm1 tm2) ty = do ftvar <- freshMVar "seq"
                                  checkTm tm1 (MkFTVar ftvar)
                                  checkTm tm2 ty
checkTm (MkUse u) t = do s <- inferUse u
                         unify t s
checkTm (MkDCon (MkDataCon k xs)) ty =
  do (dt, args, ts) <- getCtr k
     addMark
     args' <- mapM makeFlexibleTyArg args
     ts' <- mapM makeFlexible ts
     unify ty (MkDTTy dt args')
     mapM_ (uncurry checkTm) (zip xs ts')

checkSComp :: SComp Desugared -> VType Desugared -> Contextual ()
checkSComp (MkSComp xs) (MkSCTy (MkCType ps q)) =
  mapM_ (\cls -> checkCls cls ps q) xs
checkSComp (MkSComp xs) ty = mapM_ (checkCls' ty) xs
  where checkCls' :: VType Desugared -> Clause Desugared -> Contextual ()
        checkCls' ty cls@(MkCls pats tm) =
          do pushMarkCtx
             ps <- mapM (\_ -> freshPort "X") pats
             q <- freshPeg "" "X"
             checkCls cls ps q
             unify ty (MkSCTy (MkCType ps q))
             purgeMarks

freshPort :: Id -> Contextual (Port Desugared)
freshPort x = do ty <- MkFTVar <$> freshMVar x
                 return $ MkPort (MkAdj M.empty) ty

freshPeg :: Id -> Id -> Contextual (Peg Desugared)
freshPeg x y = do v <- MkAbFVar <$> freshMVar x
                  ty <- MkFTVar <$> freshMVar y
                  return $ MkPeg (MkAb v M.empty) ty

freshPegWithAb :: Ab Desugared -> Id -> Contextual (Peg Desugared)
freshPegWithAb ab x = do ty <- MkFTVar <$> freshMVar x
                         return $ MkPeg ab ty

checkCls :: Clause Desugared -> [Port Desugared] -> Peg Desugared ->
            Contextual ()
checkCls (MkCls pats tm) ports (MkPeg ab ty)
  | length pats == length ports =
    do pushMarkCtx
       putAmbient ab
       bs <- fmap concat $ mapM (uncurry checkPat) (zip pats ports)
       -- Bring any bindings in to scope for checking the term then purge the
       -- marks (and suffixes) in the context created for this clause.
       case null bs of
         True -> do checkTm tm ty
                    purgeMarks
         False -> do foldl1 (.) (map (uncurry inScope) bs) $ checkTm tm ty
                     purgeMarks
  | otherwise = throwError "number of patterns not equal to number of ports"

checkPat :: Pattern Desugared -> Port Desugared -> Contextual [TermBinding]
checkPat (MkVPat vp) (MkPort _ ty) = checkVPat vp ty
checkPat (MkCmdPat cmd xs g) (MkPort adj ty) =
  do (itf, qs, ts, y) <- getCmd cmd
     mps <- lkpItf itf (plus (MkAb MkEmpAb M.empty) adj)
     case mps of
       Nothing -> throwError $
                  "command " ++ cmd ++ " not found in adjustment " ++
                  (show $ ppAdj adj)
       Just ps -> do addMark -- localise the following type variables
                     qs' <- mapM makeFlexibleTyArg qs
                     ts' <- mapM makeFlexible ts
                     y' <- makeFlexible y
                     mapM (uncurry unifyTyArg) (zip ps qs')
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
     return $ MkSCTy $ MkCType [MkPort idAdj x] (MkPeg (plus amb adj) y)

checkVPat :: ValuePat Desugared -> VType Desugared -> Contextual [TermBinding]
checkVPat (MkVarPat x) ty = return [(MkMono x, ty)]
checkVPat (MkDataPat k xs) ty =
  do (dt, args, ts) <- getCtr k
     addMark
     args' <- mapM makeFlexibleTyArg args
     ts' <- mapM makeFlexible ts
     unify ty (MkDTTy dt args')
     bs <- fmap concat $ mapM (uncurry checkVPat) (zip xs ts')
     return bs
checkVPat (MkCharPat _) ty = unify ty MkCharTy >> return []
checkVPat (MkStrPat _) ty = unify ty desugaredStrTy >> return []
checkVPat (MkIntPat _) ty = unify ty MkIntTy >> return []
-- checkVPat p ty = throwError $ "failed to match value pattern " ++
--                  (show p) ++ " with type " ++ (show ty)

-- Replace rigid type variables with flexible ones
makeFlexible :: VType Desugared -> Contextual (VType Desugared)
makeFlexible (MkDTTy id ts) =
  MkDTTy id <$> mapM makeFlexibleTyArg ts
makeFlexible (MkSCTy cty) = MkSCTy <$> makeFlexibleCType cty
makeFlexible (MkRTVar x) = MkFTVar <$> (getContext >>= find')
  where find' BEmp = freshMVar x
        find' (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' (es :< Mark) = freshMVar x
        find' (es :< _) = find' es

makeFlexible ty = return ty

makeFlexibleAb :: Ab Desugared -> Contextual (Ab Desugared)
makeFlexibleAb (MkAb v m) = case v of
  MkAbRVar x -> do v' <- MkAbFVar <$> (getContext >>= (find' x))
                   m' <- mapM (mapM makeFlexibleTyArg) m
                   return $ MkAb v' m'
  _ -> do m' <- mapM (mapM makeFlexibleTyArg) m
          return $ MkAb v m'
  where find' x BEmp = freshMVar x
        find' x (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' x (es :< Mark) = freshMVar x
        find' x (es :< _) = find' x es

makeFlexibleTyArg :: TyArg Desugared -> Contextual (TyArg Desugared)
makeFlexibleTyArg (VArg t)  = VArg <$> makeFlexible t
makeFlexibleTyArg (EArg ab) = EArg <$> makeFlexibleAb ab

makeFlexibleAdj :: Adj Desugared -> Contextual (Adj Desugared)
makeFlexibleAdj (MkAdj m) = MkAdj <$> mapM (mapM makeFlexibleTyArg) m

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
