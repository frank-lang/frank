-- Unification implementation inspired heavily by Adam Gundry's thesis.
{-# LANGUAGE GADTs #-}
module Unification where

import qualified Data.Set as S

import Control.Monad.Except

import BwdFwd
import Syntax
import TypeCheckCommon

data Extension = Restore | Replace Suffix

restore :: Contextual Extension
restore = return Restore

replace :: Suffix -> Contextual Extension
replace = return . Replace

onTop :: (Id -> Decl -> Contextual Extension) -> Contextual ()
onTop f = popEntry >>= focus
  where focus :: Entry -> Contextual ()
        focus e@(FlexTVar x d) =
          do m <- f x d
             case m of
               Replace ext -> modify (<>< entrify ext)
               Restore -> modify (:< e)
        focus e = onTop f >> modify (:< e)

unify :: VType Desugared -> VType Desugared -> Contextual ()
unify (MkDTTy dt0 abs0 xs) (MkDTTy dt1 abs1 ys)
  | dt0 == dt1 = mapM (uncurry unifyAb) (zip abs0 abs1) >>
                 mapM_ (uncurry unify) (zip xs ys)
unify (MkSCTy cty0) (MkSCTy cty1) = unifyCType cty0 cty1
unify (MkRTVar a)  (MkRTVar b) | a == b = return ()
unify MkStringTy   MkStringTy        = return ()
unify MkIntTy      MkIntTy           = return ()
unify MkCharTy     MkCharTy          = return ()
unify (MkFTVar a)  (MkFTVar b)       = onTop $ \c d ->
  cmp (a == c) (b == c) d
  where cmp :: Bool -> Bool -> Decl -> Contextual Extension
        cmp True  True  _         = restore
        cmp True  False Hole      = replace [(a, Defn (MkFTVar b))]
        cmp False True  Hole      = replace [(b, Defn (MkFTVar a))]
        cmp True  False (Defn ty) = unify ty (MkFTVar b) >> restore
        cmp False True  (Defn ty) = unify (MkFTVar a) ty >> restore
        cmp False False _         = unify (MkFTVar a) (MkFTVar b) >> restore
unify (MkFTVar a)  ty                = solve a [] ty
unify ty           (MkFTVar a)       = solve a [] ty
unify _            _                 = throwError "Rigid-rigid mismatch"

unifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
unifyAb MkEmpAb  MkEmpAb  = return ()
unifyAb MkOpenAb MkOpenAb = return ()
unifyAb (MkAbPlus ab0 id0 xs) (MkAbPlus ab1 id1 ys) | id0 == id1 =
  unifyAb ab0 ab1 >>
  mapM_ (uncurry unify) (zip xs ys)
unifyAb _ _ = throwError "unifying abilities failed"

unifyAdj :: Adj Desugared -> Adj Desugared -> Contextual ()
unifyAdj MkIdAdj  MkIdAdj  = return ()
unifyAdj (MkAdjPlus adj0 id0 xs) (MkAdjPlus adj1 id1 ys) | id0 == id1 =
  unifyAdj adj0 adj1 >>
  mapM_ (uncurry unify) (zip xs ys)
unifyAdj _ _ = throwError "unifying adjustments failed"

unifyCType :: CType Desugared -> CType Desugared -> Contextual ()
unifyCType (MkCType xs p0) (MkCType ys p1) =
  mapM (uncurry unifyPort) (zip xs ys) >> unifyPeg p0 p1

unifyPeg :: Peg Desugared -> Peg Desugared -> Contextual ()
unifyPeg (MkPeg ab0 ty0) (MkPeg ab1 ty1) = unifyAb ab0 ab1 >> unify ty0 ty1

unifyPort :: Port Desugared -> Port Desugared -> Contextual ()
unifyPort (MkPort adj0 ty0) (MkPort adj1 ty1) = unifyAdj adj0 adj1 >>
                                                unify ty0 ty1

solve :: Id -> Suffix -> VType Desugared -> Contextual ()
solve a ext ty = onTop $ \b d ->
  case ((a == b), (S.member b (fmv ty)), d) of
    (_, _, Defn bty) -> modify (<>< entrify ext) >>
                        unify (subst bty b (MkFTVar a)) (subst bty b ty) >>
                        restore
    (True, True, Hole) -> throwError "solve: occurs check failure"
    (True, False, Hole) -> replace (ext ++ [(a, Defn ty)])
    (False, True, Hole) -> solve a ((b,d):ext) ty >> replace []
    (False, False, Hole) -> solve a ext ty >> restore

subst :: VType Desugared -> Id -> VType Desugared -> VType Desugared
subst ty x (MkDTTy dt abs xs) =
  MkDTTy dt (map (substAb ty x) abs) (map (subst ty x) xs)
subst ty x (MkSCTy cty) = MkSCTy $ substCType ty x cty
subst ty x (MkFTVar y) | x == y = ty
subst ty x (MkFTVar y) = MkFTVar y
subst ty x (MkRTVar y) = MkRTVar y
subst ty x MkStringTy = MkStringTy
subst ty x MkIntTy = MkIntTy
subst ty x MkCharTy = MkCharTy

substAb :: VType Desugared -> Id -> Ab Desugared -> Ab Desugared
substAb ty x (MkAbPlus ab itf xs) =
  MkAbPlus (substAb ty x ab) itf (map (subst ty x) xs)
substAb _ _ ab = ab

substAdj :: VType Desugared -> Id -> Adj Desugared -> Adj Desugared
substAdj ty x MkIdAdj = MkIdAdj
substAdj ty x (MkAdjPlus ab itf xs) =
  MkAdjPlus (substAdj ty x ab) itf (map (subst ty x) xs)

substCType :: VType Desugared -> Id -> CType Desugared -> CType Desugared
substCType ty x (MkCType ps peg) =
  MkCType (map (substPort ty x) ps) (substPeg ty x peg)

substPeg :: VType Desugared -> Id -> Peg Desugared -> Peg Desugared
substPeg ty x (MkPeg ab pty) = MkPeg (substAb ty x ab) (subst ty x pty)

substPort :: VType Desugared -> Id -> Port Desugared -> Port Desugared
substPort ty x (MkPort adj pty) = MkPort (substAdj ty x adj) (subst ty x pty)
