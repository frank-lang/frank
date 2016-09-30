-- Module is heavily inspired by Gundry's type inference development.
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module BwdFwd where

data Bwd a = BEmp | Bwd a :< a
           deriving (Eq, Show, Functor, Foldable, Traversable)

infixl 5 :<

(<><) :: Bwd a -> [a] -> Bwd a
xs <>< []       = xs
xs <>< (y : ys) = xs :< y <>< ys

infixl 4 <><
