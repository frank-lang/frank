{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs,ViewPatterns #-}
module TypeCheckCommon where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import BwdFwd
import FreshNames
import Syntax

-- import Text.PrettyPrint (Doc, text, sep, nest, (<+>), ($$))

newtype Contextual a = Contextual
                       { unCtx :: StateT TCState (FreshMT (Except String)) a}
--                                       TCState is carried along
--                                                Fresh variables via 'fresh'
--                                                         Exceptions possible
--                                (Except String) o FreshMT o (StateT TCState) a

type IdCmdInfoMap = M.Map Id      (Id,      [TyArg Desugared], [TyArg Desugared], [VType Desugared], VType Desugared)
--                        cmd-id   itf-id   itf-ty-vars        cmd-ty-vars        cmd-arg-tys        cmd-ret-ty
--                                          (as MkRTVar's or
--                                              MkAbRVar's)

type CtrInfoMap = M.Map Id       (Id,    [TyArg Desugared], [VType Desugared])
--                      ctr-id    dt-id  dt-ty-vars         cmd-arg-tys
--                                       (as MkRTVar's or
--                                           MkAbRVar's)

data TCState = MkTCState
  { ctx :: Context
  , amb :: Ab Desugared     -- current ambient
  , cmdMap :: IdCmdInfoMap  -- cmd-id -> (itf-id, itf-ty-vars, cmd-arg-tys, cmd-ret-ty)
  , ctrMap :: CtrInfoMap    -- ctr-id -> (dt-id, dt-ty-vars, cmd-arg-tys)
  , ms :: [Integer]         -- each entry represents one type checking phase.
                            --            counts the marks in that phase
  }

deriving instance Functor Contextual
deriving instance Applicative Contextual
deriving instance Monad Contextual
deriving instance MonadState TCState Contextual
deriving instance MonadError String Contextual
deriving instance GenFresh Contextual

data Entry = FlexMVar Id Decl
           | TermVar (Operator Desugared) (VType Desugared)
           | Mark
           deriving (Show)
data Decl = Hole
          | TyDefn (VType Desugared)
          | AbDefn (Ab Desugared)
          deriving (Show)
type Context = Bwd Entry
type TermBinding = (Operator Desugared, VType Desugared)
type Suffix = [(Id, Decl)]

-- push fresh meta variable on context (corresponds to "freshMeta" in Gundry's thesis)
freshMVar :: Id -> Contextual Id
freshMVar x = do n <- fresh
                 let s = trimVar x ++ "$f" ++ (show n)
                 modify (:< FlexMVar s Hole)
                 return s

-- free meta variables (MkFTVar's, MkAbFVar's)
fmv :: VType Desugared -> S.Set Id
fmv (DTTy _ ts _) = foldMap fmvTyArg ts
fmv (SCTy cty _) = fmvCType cty
fmv (FTVar x _) = S.singleton x
fmv (RTVar x _) = S.empty
fmv (StringTy _) = S.empty
fmv (IntTy _) = S.empty
fmv (CharTy _) = S.empty

fmvAb :: Ab Desugared -> S.Set Id
fmvAb (Ab v (ItfMap m _) _) = S.union (fmvAbMod v) (foldMap (foldMap fmvTyArg) (M.elems m))

fmvTyArg :: TyArg Desugared -> S.Set Id
fmvTyArg (VArg t _) = fmv t
fmvTyArg (EArg ab _) = fmvAb ab

fmvAbMod :: AbMod Desugared -> S.Set Id
fmvAbMod (EmpAb _) = S.empty
fmvAbMod (AbRVar _ _) = S.empty
fmvAbMod (AbFVar x _) = S.singleton x

fmvAdj :: Adj Desugared -> S.Set Id
fmvAdj (Adj (ItfMap m _) _) = foldMap (foldMap fmvTyArg) (M.elems m)

fmvCType :: CType Desugared -> S.Set Id
fmvCType (CType ps q _) = S.union (foldMap fmvPort ps) (fmvPeg q)

fmvPeg :: Peg Desugared -> S.Set Id
fmvPeg (Peg ab ty _) = S.union (fmvAb ab) (fmv ty)

fmvPort :: Port Desugared -> S.Set Id
fmvPort (Port adj ty _) = S.union (fmvAdj adj) (fmv ty)

entrify :: Suffix -> [Entry]
entrify = map $ uncurry FlexMVar

getContext :: Contextual Context
getContext = do s <- get
                return (ctx s)

putContext :: Context -> Contextual ()
putContext x = do s <- get
                  put $ s { ctx = x }

getAmbient :: Contextual (Ab Desugared)
getAmbient = do s <- get
                return (amb s)

putAmbient :: Ab Desugared -> Contextual ()
putAmbient ab = do s <- get
                   put $ s { amb = ab }

-- ms:  [...]   ->    [0, ...]
pushMarkCtx :: Contextual ()
pushMarkCtx = do s <- get
                 put $ s { ms = 0 : (ms s) }

-- ctx: [...]   ->    [..., Mark]
-- ms:  h:ts    ->    (succ h):ts
addMark :: Contextual ()
addMark = do modify (:< Mark)
             s <- get
             let h = head (ms s)
                 ts = tail (ms s)
             put $ s { ms = succ h : ts }

-- ctx: [..., E, Mark_n, ..., Mark_1, ...]   ->   [..., E]
-- ms:                                n:ts   ->   ts
purgeMarks :: Contextual ()
purgeMarks = do s <- get
                let n = head (ms s)
                put $ s { ctx = skim n (ctx s), ms = tail (ms s) }
  where -- delete everything up to (and including) the recent n Mark's
        skim :: Integer -> Context -> Context
        skim 0 es = es
        skim n (es :< Mark) = skim (n-1) es
        skim n (es :< _) = skim n es

getCmd :: Id -> Contextual (Id, [TyArg Desugared], [TyArg Desugared], [VType Desugared], VType Desugared)
getCmd cmd = get >>= \s -> case M.lookup cmd (cmdMap s) of
  Nothing -> error $ "invariant broken: " ++ show cmd ++ " not a command"
  Just (itf, qs, rs, xs, y) -> return (itf, qs, rs, xs, y)

getCmdTyVars :: Id -> Contextual [Id]
getCmdTyVars cmd = do
  (_, _, cmdTyVars, _, _) <- getCmd cmd
  return $ map filterTyVar cmdTyVars
  where
    filterTyVar :: TyArg Desugared -> Id
    filterTyVar (VArg (RTVar x _) _) = x
    filterTyVar (EArg (Ab (AbRVar x _) _ _) _) = x
    -- TODO: LC: This is a terrible invariant: refactor the way in which commands
    --           (and constructors) are represented in the Contextual. Works for
    --           now though.

-- called "popL" in Gundry's thesis
popEntry :: Contextual Entry
popEntry = do es :< e <- getContext
              putContext es
              return e

-- Alter the context by applying the provided function
modify :: (Context -> Context) -> Contextual ()
modify f = do ctx <- getContext
              putContext $ f ctx

-- Initialise the TCState, return the input program
-- Type variables of data type / interface definitions are converted into
-- rigid ty var args (which can later be made flexible for unification)
initContextual :: Prog Desugared -> Contextual (Prog Desugared)
initContextual (MkProg ttms) =
  do mapM_ f (getDataTs ttms) -- init ctrMap
     mapM_ g (getItfs ttms)   -- init cmdMap
     mapM h (getDefs ttms)    -- init ctx with [hdr: hdr-type]
     return (MkProg ttms)
  where -- data dt p_1 ... p_n = ctr_1 x_11 ... x_1m
        --                     | ...
        -- For each ctr_i add to ctrMap: ctr_i -> (dt, dt-ty-vars, xs_i)
        f :: DataT Desugared -> Contextual ()
        f (DT dt ps ctrs _) =
          let ps' = map tyVar2rigTyVarArg ps in
            mapM_ (\(Ctr ctr xs _) -> addCtr dt ctr ps' xs) ctrs

        -- interface itf p_1 .. p_m =
        --   cmd_1 : forall q_11 ... q_1n, x_11 -> ... -> q_1l -> y_1
        -- | ...
        -- For each cmd_i add to ctrMap: cmd_i -> (itf, itf-ty-vars, cmd-ty-vars, xs_i, y_i)
        g :: Itf Desugared -> Contextual ()
        g (Itf itf ps cmds _) =
          let ps' = map tyVar2rigTyVarArg ps in
            mapM_ (\(Cmd cmd qs xs y _) -> addCmd cmd itf ps' (map tyVar2rigTyVarArg qs) xs y) cmds

        -- init context for each handler id of type ty with "id := ty"
        h :: MHDef Desugared -> Contextual ()
        h (Def id ty _ a) = modify (:< TermVar (Poly id a) (SCTy ty a))

initTCState :: TCState
initTCState = MkTCState BEmp (Ab (EmpAb a) (ItfMap M.empty a) a) M.empty M.empty []
  where a = Desugared Generated

-- Only to be used for initialising the contextual monad
addCmd :: Id -> Id -> [TyArg Desugared] -> [TyArg Desugared] -> [VType Desugared] -> VType Desugared -> Contextual ()
addCmd cmd itf ps qs xs q = get >>= \s ->
  put $ s { cmdMap = M.insert cmd (itf, ps, qs, xs, q) (cmdMap s) }

addCtr :: Id -> Id -> [TyArg Desugared] -> [VType Desugared] -> Contextual ()
addCtr dt     ctr     ts         xs         = get >>= \s ->
--     dt-id  ctr-id  type-args  value-args
  put $ s { ctrMap = M.insert ctr (dt,ts,xs) (ctrMap s) }
