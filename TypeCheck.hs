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

freshFTVar :: Id -> Contextual Id
freshFTVar x = do n <- fresh
                  let s = x ++ "$f" ++ (show n)
                  modify (:< FlexTVar s Hole)
                  return s

find :: Operator -> Contextual (VType Desugared)
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

findCmd :: Id -> Adj Desugared -> Bool
findCmd cmd MkIdAdj = False
findCmd cmd (MkAdjPlus adj id _)
  | cmd == id = True
  | otherwise = findCmd cmd adj

inferUse :: Use Desugared -> Contextual (VType Desugared)
inferUse (MkOp x) = find x

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
checkTm (MkDCon (MkDataCon k xs)) (MkDTTy d ab ys) = return ()
checkTm tm ty = throwError $
                "failed to term " ++ show tm ++ " against type " ++ show ty

checkSComp :: SComp Desugared -> CType Desugared -> Contextual ()
checkSComp (MkSComp xs) (MkCType ps q) = mapM_ (\cls -> checkCls cls ps q) xs

checkCls :: Clause Desugared -> [Port Desugared] -> Peg Desugared ->
            Contextual ()
checkCls (MkCls pats tm) ports (MkPeg ab ty)
  | length pats == length ports = do putAmbient ab
                                     -- return a list of bindings?
                                     mapM_ (uncurry checkPat) (zip pats ports)
                                     checkTm tm ty
  | otherwise = throwError "number of patterns not equal to number of ports"

checkPat :: Pattern -> Port Desugared -> Contextual [TermBinding]
checkPat (MkVPat vp) (MkPort _ ty) = checkVPat vp ty
checkPat (MkCmdPat cmd ps g) (MkPort adj ty) =
  case findCmd cmd adj of
    False -> throwError $
             "command " ++ cmd ++ " not found in adjustment " ++ (show adj)
    True -> do (xs, y) <- getCmd cmd
               bs <- concatMap (uncurry checkVPat) (zip ps xs)
               kty <- contType y adj ty
               return ((MkMono g,kty) : bs)
checkPat (MkThkPat x) (MkPort adj ty) =
  do amb <- getAmbient
     return $ [(MkMono x, MkSC $ MkCType [] (MkPeg (plus amb adj) ty))]

contType :: VType Desugared -> Adj Desugared -> VType Desugared ->
            Contextual (VType Desugared)
contType x adj y =
  do amb <- getAmbient
     MkSC <$> MkCType [MkPort MkIdAdj x] (MkPeg (plus amb adj) y)

checkVPat :: ValuePat -> VType Desugared -> Contextual [TermBinding]
checkVPat (MkVarPat x) ty = return [(MkMono x, ty)]
checkVPat (MkDataPat dt0 xs0) (MkDTTy dt1 ab xs1) = return []
checkVPat (MkCharPat _) MkCharTy = return []
checkVPat (MkStrPat _) MkStringTy = return []
checkVPat (MkIntPat _) MkIntTy = return []
checkVPat _ _ = throwError "failed to match value pattern and type"

-- Replace the effect variable with the ambient
replaceAb :: Ab Desugared -> Contextual (Ab Desugared)
replaceAb MkEmpAb = return MkEmpAb
replaceAb MkOpenAb = getAmbient
replaceAb (MkAbPlus ab itf xs) = do ab' <- replaceAb ab
                                    return $ MkAbPlus ab' itf xs

plus :: Ab Desugared -> Adj Desugared -> Ab Desugared
plus ab MkIdAdj = ab
plus ab (MkAdjPlus adj itf xs) = MkAbPlus (plus ab adj) itf xs
