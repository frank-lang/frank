module Shonky.Renaming where

import Text.PrettyPrint

-- A renaming is a function from Nat to Nat that is composed as follows:
data Renaming = RenId                     -- identity [0, 1, 2, 3, ...]
              | RenS                      -- (+1)     [1, 2, 3, 4, ...]
              | RenCons Int Renaming  -- n :: r
              | RenComp Renaming Renaming -- [r1(r2(0)), r1(r2(1)), ...]
  deriving (Show, Eq)

instance Monoid Renaming where
  mempty = RenId
  mappend = RenComp

renToFun :: Renaming -> (Int -> Int)
renToFun RenId n          = n
renToFun RenS  n          = n+1
renToFun (RenCons x r) 0  = x
renToFun (RenCons x r) n  = renToFun r (n-1)
renToFun (RenComp r1 r2) n = ((renToFun r1) . (renToFun r2)) n

renRem :: Int -> Renaming
renRem n = let plusOnes = mconcat (replicate (n+1) RenS) in
           let initValues = [0 .. (n-1)] in
           foldr RenCons plusOnes initValues

renCopy :: Int -> Renaming
renCopy n = let plusOnes = mconcat (replicate n RenS) in
            let initValues = [0 .. n] in
            foldr RenCons plusOnes initValues

renSwap :: Int -> Int -> Renaming
renSwap m n = let plusOnes = mconcat (replicate (max m n + 1) RenS) in
              let initValues = map swap [0 .. (max m n)] in
              foldr RenCons plusOnes initValues
  where swap :: Int -> Int
        swap k = if k == m then n else if k == n then m else k

ppRenaming :: Renaming -> Doc
ppRenaming RenId = text "id"
ppRenaming RenS  = text "(+1)"
ppRenaming (RenCons n r) = int n <+> text "::" <+> ppRenaming r
ppRenaming (RenComp r1 r2) = ppRenaming r1 <+> text "." <+> ppRenaming r2
