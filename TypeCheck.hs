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

data Entry = FlexTVar Id Decl
           | TermVar Operator (VType Desugared) | Mark
data Decl = Hole | Defn (VType Desugared)
type Context = Bwd Entry
type Suffix = [(Id, Decl)]

newtype Contextual a = Contextual
                       (StateT Context (FreshMT (ExceptT String Identity)) a)

deriving instance Functor Contextual
deriving instance Applicative Contextual
deriving instance Monad Contextual
deriving instance MonadState Context Contextual
deriving instance MonadError String Contextual
deriving instance GenFresh Contextual

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

popEntry :: Contextual Entry
popEntry = do es :< e <- get
              put es
              return e

-- Alter the context by applying the provided function
modify :: (Context -> Context) -> Contextual ()
modify f = do ctx <- get
              put $ f ctx

freshFTVar :: Id -> Contextual Id
freshFTVar x = do n <- fresh
                  let s = x ++ "$f" ++ (show n)
                  modify (:< FlexTVar s Hole)
                  return s

find :: Operator -> Contextual (VType Desugared)
find x = get >>= find'
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
                    

