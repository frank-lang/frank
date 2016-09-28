{-# LANGUAGE GeneralizedNewtypeDeriving,StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module FreshNames where

import Control.Monad.State
import Control.Monad.Identity

newtype FreshMT m a = Fresh { unFresh :: StateT Integer m a }

deriving instance Functor m => Functor (FreshMT m)
deriving instance (Functor m, Monad m) => Applicative (FreshMT m)
deriving instance Monad m => Monad (FreshMT m)
deriving instance Monad m => MonadState Integer (FreshMT m)

class GenFresh m where
  fresh :: m Integer

instance Monad m => GenFresh (FreshMT m) where
  fresh = do n <- get
             put $ n + 1
             return n

evalFreshMT :: Monad m => FreshMT m a -> Integer -> m a
evalFreshMT = evalStateT . unFresh

evalFresh :: FreshMT Identity a -> Integer -> a
evalFresh = evalState . unFresh
