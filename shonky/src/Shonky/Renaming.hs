module Shonky.Renaming where

import Text.PrettyPrint

-- A renaming is a function from Nat to Nat. Given ms of length k and n,
-- we have
--   [m_0, ..., m_k, n, n+1, ...]
type Renaming = ([Int], Int)

renToFun :: Renaming -> (Int -> Int)
renToFun (m:_,  n) 0 = m
renToFun (_:mr, n) k = renToFun (mr, n) (k-1)
renToFun ([],   n) k = n + k

renId :: Renaming
renId = ([], 0)

renRem :: Int -> Renaming
renRem n = ([0 .. (n-1)], n+1)

renCopy :: Int -> Renaming
renCopy n = ([0 .. n], n)

renSwap :: Int -> Int -> Renaming
renSwap m n | m == n     = renId
renSwap m n = let (x, y) = (min m n, max m n) in
  ([0 .. x-1] ++ [y] ++ [x+1 .. y-1] ++ [x], y+1)

renCompose :: Renaming -> Renaming -> Renaming
renCompose r1@(ms1, n1) r2@(ms2, n2) =
  ((map (renToFun r1) ms2) ++
  (map (renToFun r1) [n2 .. length ms1 - 1]),
   n1 - length ms1 + n2)
-- TODO: LC: double-check that this is right

ppRenaming :: Renaming -> Doc
ppRenaming = text . show
