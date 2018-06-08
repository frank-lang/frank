-- Unification implementation inspired heavily by Adam Gundry's thesis.
module Unification where

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Except

import BwdFwd
import FreshNames
import Syntax
import TypeCheckCommon
import Debug

data Extension = Restore | Replace Suffix

restore :: Contextual Extension
restore = return Restore

replace :: Suffix -> Contextual Extension
replace = return . Replace

-- 1) Go through context until the first FlexMVar x:=d appears.
-- 2) Run "f" on "x:=d", resulting in either "Restore" or "Replace-by-ext"
onTop :: (Id -> Decl -> Contextual Extension) -> Contextual ()
onTop f = popEntry >>= focus
  where focus :: Entry -> Contextual ()
        focus e@(FlexMVar x d) =
          do m <- f x d
             case m of
               Replace ext -> modify (<>< entrify ext)
               Restore -> modify (:< e)
        focus e = onTop f >> modify (:< e)

-- unify 2 val tys in current context
unify :: VType Desugared -> VType Desugared -> Contextual ()                    -- corresponding rule in Gundry's thesis:
unify t0 t1 = do logBeginUnify t0 t1
                 unify' t0 t1
                 logEndUnify t0 t1
  where
  unify' (DTTy dt0 ts0 _) (DTTy dt1 ts1 _)                                      -- decompose (modified)
    | dt0 == dt1 && eqLens ts0 ts1 =
      zipWithM_ unifyTyArg ts0 ts1
  unify' v1@(DTTy dt0 ts0 _) v2@(DTTy dt1 ts1 _)                                -- decompose fails
    | not $ eqLens ts0 ts1 =
    throwError $ errorUnifDiffNumberArgs v1 v2
  unify' (SCTy cty0 _)   (SCTy cty1 _)        = unifyCType cty0 cty1
  unify' (RTVar a _)     (RTVar b _) | a == b = return ()
  unify' (IntTy _)       (IntTy _)            = return ()
  unify' (CharTy _)      (CharTy _)           = return ()
  unify' fta@(FTVar a _) ftb@(FTVar b _)      = onTop $ \c d ->
    cmp (a == c) (b == c) d
    where cmp :: Bool -> Bool -> Decl -> Contextual Extension
          cmp True  True  _           = restore                                 -- idle
          cmp True  False Hole        = replace [(a, TyDefn ftb)]               -- define
          cmp False True  Hole        = replace [(b, TyDefn fta)]               -- define
          cmp True  False (TyDefn ty) = unify ty ftb >> restore                 -- subs
          cmp False True  (TyDefn ty) = unify fta ty >> restore                 -- subs
          cmp False False _           = unify fta ftb >> restore                -- skip-ty
          cmp _     _     (AbDefn _)  = error "unification invariant broken"
  unify' (FTVar x a)     ty                   = solve x a [] ty                 -- inst
  unify' ty              (FTVar y b)          = solve y b [] ty                 -- inst
  unify' t               s                    = throwError $ errorUnifTys t s

-- unify 2 eff tys in current context
unifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
unifyAb ab0@(Ab v0 m0 a) ab1@(Ab v1 m1 b) =
  do logBeginUnifyAb ab0 ab1
     -- expand abs by resolving all flexible variables
     ab0' <- expandAb ab0
     ab1' <- expandAb ab1
     -- then unify
     unifyAb' ab0' ab1'
     logEndUnifyAb ab0 ab1
  where unifyAb' :: Ab Desugared -> Ab Desugared -> Contextual ()
        -- Same eff ty vars leaves nothing to unify but instantiat's m0, m1
        unifyAb' ab0@(Ab v0 m1 _) ab1@(Ab v1 m2 _) | strip v0 == strip v1 =
          catchError (unifyItfMap m1 m2) (unifyAbError ab0 ab1)
        -- Both eff ty vars are flexible
        unifyAb' (Ab (AbFVar x a') m1 a) (Ab (AbFVar y b') m2 b) =
          do -- For same occurrences of interfaces, their instantiat's must coincide
             unifyItfMap (intersectItfMap m1 m2) (intersectItfMap m2 m1)
             v <- AbFVar <$> freshMVar "£" <*> pure (Desugared Generated)
             solveForEVar x a' [] (Ab v (m2 `cutItfMapSuffix` m1) a)  -- TODO: LC: locations assigned correctly?
             solveForEVar y b' [] (Ab v (m1 `cutItfMapSuffix` m2) b)
        -- One eff ty var is flexible, the other one either empty or rigid
        unifyAb' (Ab (AbFVar x a') m1 _) (Ab v m2 b)
          | isItfMapEmpty (cutItfMapSuffix m1 m2) =
            do unifyItfMap (intersectItfMap m1 m2) (intersectItfMap m2 m1)
               solveForEVar x a' [] (Ab v (m2 `cutItfMapSuffix` m1) b)   -- TODO: LC: locations assigned correctly?
        unifyAb' (Ab v m1 a) (Ab (AbFVar y b') m2 _)
          | isItfMapEmpty (cutItfMapSuffix m2 m1) =
            do unifyItfMap (intersectItfMap m1 m2) (intersectItfMap m2 m1)
               solveForEVar y b' [] (Ab v (m1 `cutItfMapSuffix` m2) a)   -- TODO: LC: locations assigned correctly?
        -- In any other case
        unifyAb' ab0 ab1 = throwError $ errorUnifAbs ab0 ab1

unifyTyArg :: TyArg Desugared -> TyArg Desugared -> Contextual ()
unifyTyArg (VArg t0 _) (VArg t1 _) = unify t0 t1
unifyTyArg (EArg ab0 _) (EArg ab1 _) = unifyAb ab0 ab1
unifyTyArg arg0 arg1 = throwError $ errorUnifTyArgs arg0 arg1

unifyAbError :: Ab Desugared -> Ab Desugared -> String -> Contextual ()
unifyAbError ab0 ab1 _ = throwError $ errorUnifAbs ab0 ab1

-- Given two interface maps, check that each instantiation has a unifiable
-- counterpart in the other ability and unify.
unifyItfMap :: ItfMap Desugared -> ItfMap Desugared -> Contextual ()
unifyItfMap m0@(ItfMap m0' a) m1@(ItfMap m1' b) = do
  mapM_ (unifyItfMap' m1) (M.toList m0')
  mapM_ (unifyItfMap' m0) (M.toList m1')
  where unifyItfMap' :: ItfMap Desugared -> (Id, Bwd [TyArg Desugared]) -> Contextual ()
        unifyItfMap' (ItfMap m _) (x, insts) = case M.lookup x m of
          Nothing -> throwError $ errorUnifItfMaps m0 m1
          Just insts' -> if length insts /= length insts' then throwError $ errorUnifItfMaps m0 m1
                         else zipWithM_ (zipWithM_ unifyTyArg) (bwd2fwd insts) (bwd2fwd insts')

unifyAdj :: Adj Desugared -> Adj Desugared -> Contextual ()
unifyAdj (Adj m0 _) (Adj m1 _) = unifyItfMap m0 m1

unifyCType :: CType Desugared -> CType Desugared -> Contextual ()
unifyCType (CType xs p0 _) (CType ys p1 _) =
  zipWithM_ unifyPort xs ys >> unifyPeg p0 p1

unifyPeg :: Peg Desugared -> Peg Desugared -> Contextual ()
unifyPeg (Peg ab0 ty0 _) (Peg ab1 ty1 _) = unifyAb ab0 ab1 >> unify ty0 ty1

unifyPort :: Port Desugared -> Port Desugared -> Contextual ()
unifyPort (Port adjs0 ty0 _) (Port adjs1 ty1 _) = unifyAdjs adjs0 adjs1 >>
                                                                  unify ty0 ty1

-- unify a meta variable "x" with a type "ty"
solve :: Id -> Desugared -> Suffix -> VType Desugared -> Contextual ()
solve x a ext ty = do logBeginSolve x ext ty
                      solve'
                      logEndSolve x ext ty
  where
  solve' = onTop $ \y d -> do
    logSolveStep (x == y, S.member y (fmv ty), d)
    case (x == y, S.member y (fmv ty), d) of
      (_,     _,     TyDefn bty) -> modify (<>< entrify ext) >>                 -- inst-subs (val ty var)
                                    unify (subst bty y (FTVar x a)) (subst bty y ty) >>
                                    restore
      (_,     _,     AbDefn ab) ->  modify (<>< entrify ext) >>                 -- inst-subs (eff ty var)
                                    unify (substEVar ab y (FTVar x a)) (substEVar ab y ty) >>
                                    restore
      (True,  True,  Hole) -> throwError errorUnifSolveOccurCheck
      (True,  False, Hole) -> replace (ext ++ [(x, TyDefn ty)])                 -- inst-define
      (False, True,  Hole) -> solve x a ((y, d):ext) ty >> replace []           -- inst-depend
      (False, False, Hole) -> solve x a ext ty >> restore                       -- inst-skip-ty

solveForEVar :: Id -> Desugared -> Suffix -> Ab Desugared -> Contextual ()
solveForEVar x a ext ab = onTop $ \y d ->
  case (x == y, S.member y (fmvAb ab), d) of
    (_, _, AbDefn ab') ->
      let vab = Ab (AbFVar x a) (ItfMap M.empty a) a in
      modify (<>< entrify ext) >>
      unifyAb (substEVarAb ab' y vab) (substEVarAb ab' y ab) >>
      restore
    (True, True, Hole) -> throwError errorUnifSolveOccurCheck
    (True, False, Hole) -> replace (ext ++ [(x, AbDefn ab)])
    (False, True, _) -> solveForEVar x a ((y, d):ext) ab >> replace []
    (False, False, _) -> solveForEVar x a ext ab >> restore
    (_, _, TyDefn _) ->
      error "solveForEVar invariant broken: reached impossible case"

{- Substitute "ty" for "x" in X -}

subst :: VType Desugared -> Id -> VType Desugared -> VType Desugared
subst ty x (DTTy dt ts a) = DTTy dt (map (substTyArg ty x) ts) a
subst ty x (SCTy cty a) = SCTy (substCType ty x cty) a
subst ty x (FTVar y a) | x == y = ty
subst _ _ ty = ty

substAb :: VType Desugared -> Id -> Ab Desugared -> Ab Desugared
substAb ty x (Ab v (ItfMap m a') a) = Ab v (ItfMap m' a') a
  where m' = fmap (fmap (map (substTyArg ty x))) m

substTyArg :: VType Desugared -> Id -> TyArg Desugared -> TyArg Desugared
substTyArg ty x (VArg t a) = VArg (subst ty x t) a
substTyArg ty x (EArg ab a) = EArg (substAb ty x ab) a

substAdj :: VType Desugared -> Id -> Adj Desugared -> Adj Desugared
substAdj ty x (Adj (ItfMap m a') a) = Adj (ItfMap m' a') a
  where m' = M.map (fmap (map (substTyArg ty x))) m

substCType :: VType Desugared -> Id -> CType Desugared -> CType Desugared
substCType ty x (CType ps peg a) =
  CType (map (substPort ty x) ps) (substPeg ty x peg) a

substPeg :: VType Desugared -> Id -> Peg Desugared -> Peg Desugared
substPeg ty x (Peg ab pty a) = Peg (substAb ty x ab) (subst ty x pty) a

substPort :: VType Desugared -> Id -> Port Desugared -> Port Desugared
substPort ty x (Port adj pty a) = Port (substAdj ty x adj) (subst ty x pty) a

substEVar :: Ab Desugared -> Id -> VType Desugared -> VType Desugared
substEVar ab x (DTTy dt ts a) = DTTy dt (map (substEVarTyArg ab x) ts) a
substEVar ab x (SCTy cty a) = SCTy (substEVarCType ab x cty) a
substEVar _ _ ty = ty

-- substitute "ab" for "x" in AB
substEVarAb :: Ab Desugared -> Id -> Ab Desugared -> Ab Desugared
substEVarAb ab@(Ab v m' _) x (Ab (AbFVar y a) (ItfMap m ann') ann) | x == y =
  Ab v m'' ann
  where m'' = plusItfMap m' (ItfMap (fmap (fmap (map (substEVarTyArg ab x))) m) ann')
substEVarAb ab x (Ab v (ItfMap m a') a) = Ab v (ItfMap (M.map (fmap (map (substEVarTyArg ab x))) m) a') a

substEVarTyArg :: Ab Desugared -> Id -> TyArg Desugared -> TyArg Desugared
substEVarTyArg ab x (VArg t a)  = VArg (substEVar ab x t) a
substEVarTyArg ab x (EArg ab' a) = EArg (substEVarAb ab x ab') a

substEVarAdj :: Ab Desugared -> Id -> Adj Desugared -> Adj Desugared
substEVarAdj ab x (Adj (ItfMap m a') a) = Adj (ItfMap m' a') a
  where m' = M.map (fmap (map (substEVarTyArg ab x))) m

substEVarCType :: Ab Desugared -> Id -> CType Desugared -> CType Desugared
substEVarCType ab x (CType ps peg a) =
  CType (map (substEVarPort ab x) ps) (substEVarPeg ab x peg) a

substEVarPeg :: Ab Desugared -> Id -> Peg Desugared -> Peg Desugared
substEVarPeg ab' x (Peg ab pty a) =
  Peg (substEVarAb ab' x ab) (substEVar ab' x pty) a

substEVarPort :: Ab Desugared -> Id -> Port Desugared -> Port Desugared
substEVarPort ab x (Port adj pty a) =
  Port (substEVarAdj ab x adj) (substEVar ab x pty) a

{- Helpers -}

eqLens :: [a] -> [a] -> Bool
eqLens xs ys = length xs == length ys
