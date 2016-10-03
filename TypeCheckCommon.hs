{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
module TypeCheckCommon where

import qualified Data.Set as S

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import BwdFwd
import FreshNames
import Syntax

newtype Contextual a = Contextual
                       (StateT TCState (FreshMT (ExceptT String Identity)) a)

data TCState = MkTCState { ctx :: Context
                         , amb :: Ab Desugared }

deriving instance Functor Contextual
deriving instance Applicative Contextual
deriving instance Monad Contextual
deriving instance MonadState TCState Contextual
deriving instance MonadError String Contextual
deriving instance GenFresh Contextual

data Entry = FlexTVar Id Decl
           | TermVar Operator (VType Desugared) | Mark
data Decl = Hole | Defn (VType Desugared)
type Context = Bwd Entry
type TermBinding = (Operator, VType Desugared)
type Suffix = [(Id, Decl)]

fmv :: VType Desugared -> S.Set Id
fmv (MkDTTy _ ab xs) = S.union (fmvAb ab) (foldMap fmv xs)
fmv (MkSCTy cty) = fmvCType cty
fmv (MkFTVar x) = S.singleton x
fmv (MkRTVar x) = S.empty
fmv MkStringTy = S.empty
fmv MkIntTy = S.empty
fmv MkCharTy = S.empty

fmvAb :: Ab Desugared -> S.Set Id
fmvAb MkEmpAb = S.empty
fmvAb MkOpenAb = S.empty -- possibly return some constant ftvar here?
fmvAb (MkAbPlus ab _ xs) = S.union (fmvAb ab) (foldMap fmv xs)

fmvAdj :: Adj Desugared -> S.Set Id
fmvAdj MkIdAdj = S.empty
fmvAdj (MkAdjPlus adj _ xs) = S.union (fmvAdj adj) (foldMap fmv xs)

fmvCType :: CType Desugared -> S.Set Id
fmvCType (MkCType ps q) = S.union (foldMap fmvPort ps) (fmvPeg q)

fmvPeg :: Peg Desugared -> S.Set Id
fmvPeg (MkPeg ab ty) = S.union (fmvAb ab) (fmv ty)

fmvPort :: Port Desugared -> S.Set Id
fmvPort (MkPort adj ty) = S.union (fmvAdj adj) (fmv ty)

entrify :: Suffix -> [Entry]
entrify = map $ uncurry FlexTVar

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

getCmd :: Id -> Contextual ([VType Desugared],VType Desugared)
getCmd cmd = return ([],MkIntTy)

popEntry :: Contextual Entry
popEntry = do es :< e <- getContext
              putContext es
              return e

-- Alter the context by applying the provided function
modify :: (Context -> Context) -> Contextual ()
modify f = do ctx <- getContext
              putContext $ f ctx
