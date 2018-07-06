module Shonky.Renaming where

import Text.PrettyPrint

-- A renaming is a function from Nat to Nat that is composed as follows:
data Renaming = RenId                     -- identity [0, 1, 2, 3, ...]
              | RenS                      -- (+1)     [1, 2, 3, 4, ...]
              | RenCons Int Renaming  -- n :: r
              | RenComp Renaming Renaming -- [r1(r2(0)), r1(r2(1)), ...]
  deriving (Show, Eq)

-- A renaming is a function from Nat to Nat. Given ms of length k and n,
-- we have
--   [m_0, ..., m_k, n, n+1, ...]
type RRenaming = ([Int], Int)

instance Monoid Renaming where
  mempty = RenId
  mappend = RenComp

renToFun :: Renaming -> (Int -> Int)
renToFun RenId n          = n
renToFun RenS  n          = n+1
renToFun (RenCons x r) 0  = x
renToFun (RenCons x r) n  = renToFun r (n-1)
renToFun (RenComp r1 r2) n = ((renToFun r1) . (renToFun r2)) n

rrenToFun :: RRenaming -> (Int -> Int)
rrenToFun (m:_,  n) 0 = m
rrenToFun (_:mr, n) k = rrenToFun (mr, n) (k-1)
rrenToFun ([],   n) k = n + k

rrenId :: RRenaming
rrenId = ([], 0)

renRem :: Int -> Renaming
renRem n = let plusOnes = mconcat (replicate (n+1) RenS) in
           let initValues = [0 .. (n-1)] in
           foldr RenCons plusOnes initValues

rrenRem :: Int -> RRenaming
rrenRem n = ([0 .. (n-1)], n+1)

renCopy :: Int -> Renaming
renCopy n = let plusOnes = mconcat (replicate n RenS) in
            let initValues = [0 .. n] in
            foldr RenCons plusOnes initValues

rrenCopy :: Int -> RRenaming
rrenCopy n = ([0 .. n], n)

renSwap :: Int -> Int -> Renaming
renSwap m n = let plusOnes = mconcat (replicate (max m n + 1) RenS) in
              let initValues = map swap [0 .. (max m n)] in
              foldr RenCons plusOnes initValues
  where swap :: Int -> Int
        swap k = if k == m then n else if k == n then m else k

rrenSwap :: Int -> Int -> RRenaming
rrenSwap m n | m == n   = rrenId
rrenSwap m n = let (x, y) = (min m n, max m n) in
  ([0 .. x-1] ++ [y] ++ [x+1 .. y-1] ++ [x], y+1)

rrenCompose :: RRenaming -> RRenaming -> RRenaming
rrenCompose r1@(ms1, n1) r2@(ms2, n2) =
  ((map (rrenToFun r1) ms2) ++
  (map (rrenToFun r1) [n2 .. length ms1 - 1]),
   n1 - length ms1 + n2)
-- TODO: LC: double-check this is right

ppRenaming :: Renaming -> Doc
ppRenaming RenId = text "id"
ppRenaming RenS  = text "(+1)"
ppRenaming (RenCons n r) = int n <+> text "::" <+> ppRenaming r
ppRenaming (RenComp r1 r2) = ppRenaming r1 <+> text "." <+> ppRenaming r2

ppRRenaming :: RRenaming -> Doc
ppRRenaming = text . show
