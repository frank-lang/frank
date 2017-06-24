-- Module is heavily inspired by Gundry's type inference development.
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module BwdFwd where

import Text.PrettyPrint (Doc, text, sep, nest, (<+>), ($$))

data Bwd a = BEmp | Bwd a :< a
           deriving (Eq, Show, Functor, Foldable, Traversable)

infixl 5 :<

(<><) :: Bwd a -> [a] -> Bwd a
xs <>< []       = xs
xs <>< (y : ys) = xs :< y <>< ys

infixl 4 <><

bwd2fwd :: Bwd a -> [a]
bwd2fwd sx = bwd2fwd' sx [] where
  bwd2fwd' BEmp       acc = acc
  bwd2fwd' (rx :< x) acc = bwd2fwd' rx (x:acc)
