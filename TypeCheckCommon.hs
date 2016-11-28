{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
module TypeCheckCommon where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import Debug.Trace

import BwdFwd
import FreshNames
import Syntax

newtype Contextual a = Contextual
                       { unCtx :: StateT TCState (FreshMT (Except String)) a}

type IdCmdInfoMap = M.Map Id (Id,[VType Desugared],
                              [VType Desugared],VType Desugared)
type CtrInfoMap = M.Map Id (Id,[AbMod Desugared],
                            [VType Desugared],[VType Desugared])

data TCState = MkTCState
  { ctx :: Context
  , amb :: Ab Desugared
  , cmdMap :: IdCmdInfoMap
  , ctrMap :: CtrInfoMap
  , ms :: [Integer] -- the number of markers separating localities in the
                    -- current scope
  }

deriving instance Functor Contextual
deriving instance Applicative Contextual
deriving instance Monad Contextual
deriving instance MonadState TCState Contextual
deriving instance MonadError String Contextual
deriving instance GenFresh Contextual

data Entry = FlexMVar Id Decl
           | TermVar Operator (VType Desugared) | Mark
           deriving (Show)
data Decl = Hole | TyDefn (VType Desugared) | AbDefn (Ab Desugared)
          deriving (Show)
type Context = Bwd Entry
type TermBinding = (Operator, VType Desugared)
type Suffix = [(Id, Decl)]

freshMVar :: Id -> Contextual Id
freshMVar x = do n <- fresh
                 let s = trimVar x ++ "$f" ++ (show n)
                 modify (:< FlexMVar s Hole)
                 return s

fmv :: VType Desugared -> S.Set Id
fmv (MkDTTy _ abs xs) = S.union (foldMap fmvAb abs) (foldMap fmv xs)
fmv (MkSCTy cty) = fmvCType cty
fmv (MkFTVar x) = S.singleton x
fmv (MkRTVar x) = S.empty
fmv MkStringTy = S.empty
fmv MkIntTy = S.empty
fmv MkCharTy = S.empty

fmvAb :: Ab Desugared -> S.Set Id
fmvAb (MkAb v m) = S.union (fmvAbMod v) (foldMap (foldMap fmv) (M.elems m))

fmvAbMod :: AbMod Desugared -> S.Set Id
fmvAbMod MkEmpAb = S.empty
fmvAbMod (MkAbRVar _) = S.empty
fmvAbMod (MkAbFVar x) = S.singleton x

fmvAdj :: Adj Desugared -> S.Set Id
fmvAdj (MkAdj m) = foldMap (foldMap fmv) (M.elems m)

fmvCType :: CType Desugared -> S.Set Id
fmvCType (MkCType ps q) = S.union (foldMap fmvPort ps) (fmvPeg q)

fmvPeg :: Peg Desugared -> S.Set Id
fmvPeg (MkPeg ab ty) = S.union (fmvAb ab) (fmv ty)

fmvPort :: Port Desugared -> S.Set Id
fmvPort (MkPort adj ty) = S.union (fmvAdj adj) (fmv ty)

entrify :: Suffix -> [Entry]
entrify = map $ uncurry FlexMVar

liftAbMod :: AbMod a -> Ab a
liftAbMod v = MkAb v M.empty

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

pushMarkCtx :: Contextual ()
pushMarkCtx = do s <- get
                 put $ s { ms = 0 : (ms s) }

addMark :: Contextual ()
addMark = do modify (:< Mark)
             s <- get
             let h = head (ms s)
                 ts = tail (ms s)
             put $ s { ms = succ h : ts }

purgeMarks :: Contextual ()
purgeMarks = do s <- get
                let n = head (ms s)
                put $ s { ctx = skim n (ctx s), ms = tail (ms s) }
  where skim :: Integer -> Context -> Context
        skim 0 es = es
        skim n (es :< Mark) = skim (n-1) es
        skim n (es :< _) = skim n es
        
getCmd :: Id -> Contextual (Id,[VType Desugared],
                            [VType Desugared],VType Desugared)
getCmd cmd = get >>= \s -> case M.lookup cmd (cmdMap s) of
  Nothing -> error $ "invariant broken: " ++ show cmd ++ " not a command"
  Just (itf, qs, xs, y) -> return (itf, qs, xs, y)

getCtr :: Id -> Contextual (Id,[AbMod Desugared],
                            [VType Desugared],[VType Desugared])
getCtr k = get >>= \s -> case M.lookup k (ctrMap s) of
  Nothing -> throwError $
             "'" ++ k ++ "' is not a constructor"
  Just (dt, es, ps, xs) -> return (dt, es, ps, xs)

popEntry :: Contextual Entry
popEntry = do es :< e <- getContext
              putContext es
              return e

-- Alter the context by applying the provided function
modify :: (Context -> Context) -> Contextual ()
modify f = do ctx <- getContext
              putContext $ f ctx

initContextual :: Prog Desugared -> Contextual (Prog Desugared)
initContextual (MkProg xs) =
  do mapM_ f (getDataTs xs)
     mapM_ g (getItfs xs)
     mapM h (getDefs xs)
     return (MkProg xs)
  where f :: DataT Desugared -> Contextual ()
        f (MkDT dt es ps cs) = let ps' = map MkRTVar ps in
          let es' = map MkAbRVar es in
          mapM_ (\(MkCtr ctr xs) -> addCtr dt ctr es' ps' xs) cs

        g :: Itf Desugared -> Contextual ()
        g (MkItf itf ps cs) = let ps' = map MkRTVar ps in
          mapM_ (\(MkCmd x xs y) -> addCmd x itf ps' xs y) cs

        h :: MHDef Desugared -> Contextual ()
        h (MkDef id ty _) = modify (:< TermVar (MkPoly id) (MkSCTy ty))

initTCState :: TCState
initTCState = MkTCState BEmp (MkAb MkEmpAb M.empty) M.empty M.empty []

-- Only to be used for initialising the contextual monad
addCmd :: Id -> Id -> [VType Desugared] -> [VType Desugared] ->
          VType Desugared -> Contextual ()
addCmd cmd itf ps xs q = get >>= \s ->
  put $ s { cmdMap = M.insert cmd (itf, ps, xs, q) (cmdMap s) }

addCtr :: Id -> Id -> [AbMod Desugared] -> [VType Desugared] ->
          [VType Desugared] -> Contextual ()
addCtr dt ctr es ps xs = get >>= \s ->
  put $ s { ctrMap = M.insert ctr (dt,es,ps,xs) (ctrMap s) }
