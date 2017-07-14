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

dropBwd :: Int -> Bwd a -> Bwd a  --TODO: LC: implement using Foldable
dropBwd 0 sx = sx
dropBwd n (rx :< x) = dropBwd (n-1) rx
dropBwd n BEmp = BEmp

takeBwd :: Int -> Bwd a -> Bwd a  --TODO: LC: implement using Foldable
takeBwd 0 sx = BEmp
takeBwd n (rx :< x) = (takeBwd (n-1) rx) :< x
takeBwd n BEmp = BEmp

bwd2fwd :: Bwd a -> [a]  --TODO: LC: implement using Foldable
bwd2fwd sx = bwd2fwd' sx [] where
  bwd2fwd' BEmp      acc = acc
  bwd2fwd' (rx :< x) acc = bwd2fwd' rx (x:acc)

fwd2bwd :: [a] -> Bwd a
fwd2bwd = foldl (:<) BEmp
