{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

{-------------------}
{-- Syntax description: raw syntax comes from the parser and preprocessed into
    refined syntax. --}

class NotRaw a where
  idNotRaw :: a -> a

class NotDesugared a where
  idNotDesugared :: a -> a

data Raw = MkRaw

instance NotDesugared Raw where
  idNotDesugared = Prelude.id

data Refined = MkRefined

instance NotDesugared Refined where
  idNotDesugared = Prelude.id

instance NotRaw Refined where
  idNotRaw = Prelude.id

data Desugared = MkDesugared

instance NotRaw Desugared where
  idNotRaw = Prelude.id

{-- The raw syntax as parsed in from the file and the refined syntax produced
    by a preprocessing stage before typechecking are simultaneously defined
    using GADT syntax. --}

data Prog a = MkProg [TopTm a]
            deriving (Show, Eq)

{---------------}
{- Parts of the grammar specific to the raw syntax. -}

-- A top-level multihandler signature and clause.
data MHSig = MkSig Id (CType Raw)
             deriving (Show, Eq)

data MHCls = MkMHCls Id (Clause Raw)
           deriving (Show, Eq)

{---------------}
{- Parts of the grammar specific to the refined syntax. -}
data MHDef a = MkDef Id (CType a) [Clause a]
           deriving (Show, Eq)

data Operator = MkMono Id | MkPoly Id | MkCmdId Id
              deriving (Show, Eq)

data Use a = MkOp Operator | MkApp Operator [Tm a]
           deriving (Show, Eq)

data DataCon a = MkDataCon Id [Tm a]
               deriving (Show, Eq)

{---------------}
{- Parts of the grammar independent of the syntax. -}

-- A raw term collects multihandler signatures and clauses separately. A
-- refined top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTm a where
  MkDataTm :: DataT a -> TopTm a
  MkItfTm :: Itf a -> TopTm a
  MkSigTm :: MHSig -> TopTm Raw
  MkClsTm :: MHCls -> TopTm Raw
  MkDefTm :: NotRaw a => MHDef a -> TopTm a

deriving instance (Show) (TopTm a)
deriving instance (Eq) (TopTm a)

data Tm a where
  MkRawId :: Id -> Tm Raw
  MkRawComb :: Id -> [Tm Raw] -> Tm Raw
  MkSC :: SComp a -> Tm a
  MkLet :: Tm a
  MkStr :: String -> Tm a
  MkInt :: Integer -> Tm a
  MkChar :: Char -> Tm a
  MkTmSeq :: Tm a -> Tm a -> Tm a
  MkUse :: NotRaw a => Use a -> Tm a
  MkDCon :: NotRaw a => DataCon a -> Tm a

deriving instance (Show) (Tm a)
deriving instance (Eq) (Tm a)

-- A clause for a multihandler definition
data Clause a = MkCls [Pattern] (Tm a)
              deriving (Show, Eq)

data SComp a = MkSComp [Clause a]
           deriving (Show, Eq)

data DataT a = MkDT Id [Id] [Id] [Ctr a]
             deriving (Show, Eq)

data Itf a = MkItf Id [Id] [Cmd a]
           deriving (Show, Eq)

data Ctr a = MkCtr Id [VType a]
           deriving (Show, Eq)

data Cmd a = MkCmd Id [VType a] (VType a)
           deriving (Show, Eq)

data Pattern = MkVPat ValuePat | MkCmdPat Id [ValuePat] Id | MkThkPat Id
             deriving (Show, Eq)

data ValuePat = MkVarPat Id | MkDataPat Id [ValuePat] | MkIntPat Integer
              | MkCharPat Char | MkStrPat String
              deriving (Show, Eq)

type Id = String

-- Type hierarchy
data CType a = MkCType [Port a] (Peg a)
           deriving (Show, Eq)

data Port a = MkPort (Adj a) (VType a)
          deriving (Show, Eq)

data Peg a = MkPeg (Ab a) (VType a)
           deriving (Show, Eq)

data VType a where
  MkDTTy :: Id -> [Ab a] -> [VType a] -> VType a
  MkSCTy :: CType a -> VType a
  MkTVar :: NotDesugared a => Id -> VType a
  MkRTVar :: Id -> VType Desugared
  MkFTVar :: Id -> VType Desugared
  MkStringTy :: VType a
  MkIntTy :: VType a
  MkCharTy :: VType a

deriving instance (Show) (VType a)
deriving instance (Eq) (VType a)

-- Adjustments
data Adj a = MkIdAdj | MkAdjPlus (Adj a) Id [VType a]
           deriving (Show, Eq)

-- Abilities
data Ab a = MkEmpAb | MkAbPlus (Ab a) Id [VType a] | MkOpenAb | MkAbVar Id
          deriving (Show, Eq)

getItfs :: [TopTm a] -> [Itf a]
getItfs xs = getItfs' xs []
  where getItfs' :: [TopTm a] -> [Itf a] -> [Itf a]
        getItfs' ((MkItfTm itf) : xs) ys = getItfs' xs (itf : ys)
        getItfs' (_ : xs) ys = getItfs' xs ys
        getItfs' [] ys = ys

getCmds :: Itf a -> [Cmd a]
getCmds (MkItf _ _ xs) = xs

collectINames :: [Itf a] -> [Id]
collectINames ((MkItf itf _ _) : xs) = itf : (collectINames xs)
collectINames [] = []

getDataTs :: [TopTm a] -> [DataT a]
getDataTs xs = getDataTs' xs []
  where getDataTs' :: [TopTm a] -> [DataT a] -> [DataT a]
        getDataTs' ((MkDataTm dt) : xs) ys = getDataTs' xs (dt : ys)
        getDataTs' (_ : xs) ys = getDataTs' xs ys
        getDataTs' [] ys = ys

getCtrs :: DataT a -> [Ctr a]
getCtrs (MkDT _ _ _ xs) = xs

collectDTNames :: [DataT a] -> [Id]
collectDTNames ((MkDT dt _ _ _) : xs) = dt : (collectDTNames xs)
collectDTNames [] = []

-- Convert ability to a list of interface names and effect variables
abToList :: Ab a -> [Id]
abToList MkEmpAb = []
abToList (MkAbVar id) = [id]
abToList MkOpenAb = []
abToList (MkAbPlus ab id _) = id : abToList ab

-- Substitute the ability for the distinguished effect variable in the type.
substOpenAb :: Ab a -> VType a -> VType a
substOpenAb ab (MkDTTy id abs xs) =
  MkDTTy id (map (substOpenAbAb ab) abs) (map (substOpenAb ab) xs)
substOpenAb ab (MkSCTy cty) = MkSCTy $ substOpenAbCType ab cty
substOpenAb _ ty = ty

substOpenAbAb :: Ab a -> Ab a -> Ab a
substOpenAbAb ab MkEmpAb = MkEmpAb
substOpenAbAb ab MkOpenAb = ab
substOpenAbAb ab (MkAbVar x) = MkAbVar x
substOpenAbAb ab (MkAbPlus ab' x ts) =
  MkAbPlus (substOpenAbAb ab' ab) x (map (substOpenAb ab) ts)

substOpenAbAdj :: Ab a -> Adj a -> Adj a
substOpenAbAdj ab MkIdAdj = MkIdAdj
substOpenAbAdj ab (MkAdjPlus adj itf xs) =
  MkAdjPlus (substOpenAbAdj ab adj) itf (map (substOpenAb ab) xs)

substOpenAbCType :: Ab a -> CType a -> CType a
substOpenAbCType ab (MkCType ps q) =
  MkCType (map (substOpenAbPort ab) ps) (substOpenAbPeg ab q)

substOpenAbPeg :: Ab a -> Peg a -> Peg a
substOpenAbPeg ab (MkPeg ab' ty) =
  MkPeg (substOpenAbAb ab ab') (substOpenAb ab ty)

substOpenAbPort :: Ab a -> Port a -> Port a
substOpenAbPort ab (MkPort adj ty) =
  MkPort (substOpenAbAdj ab adj) (substOpenAb ab ty)

plus :: Ab a -> Adj a -> Ab a
plus ab MkIdAdj = ab
plus ab (MkAdjPlus adj itf xs) = MkAbPlus (plus ab adj) itf xs
