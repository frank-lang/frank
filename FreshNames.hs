{-# LANGUAGE GeneralizedNewtypeDeriving,StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances,UndecidableInstances #-}
module FreshNames where

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Except

-- this monad will supply fresh and is really a state monad transformer
newtype FreshMT m a = Fresh { unFresh :: StateT Integer m a }
                      deriving (Functor, Applicative, Monad,
                                MonadState Integer)

class Monad m => GenFresh m where
  fresh :: m Integer

evalFreshMT :: Monad m => FreshMT m a -> m a
evalFreshMT m = evalStateT (unFresh m) 0

evalFresh :: FreshMT Identity a -> a
evalFresh m = evalState (unFresh m) 0

instance Monad m => GenFresh (FreshMT m) where
  fresh = do n <- get
             put $ n + 1
             return n

instance GenFresh m => GenFresh (StateT s m) where
  fresh = lift fresh

instance MonadTrans FreshMT where
  lift = Fresh . lift

instance MonadError e m => MonadError e (FreshMT m) where
  throwError = lift . throwError
  catchError m h = Fresh $ catchError (unFresh m) (unFresh . h)
