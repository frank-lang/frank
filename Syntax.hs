{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

{-------------------}
{-- Syntax description: raw syntax comes from the parser and preprocessed into
    refined syntax. --}

data SyntaxDesc = Raw | Refined deriving (Show, Eq)

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
data MHDef = MkDef Id (VType Refined) [Clause Refined]
           deriving (Show, Eq)

data Use = MkIdent Id | MkApp Id [Tm Refined]
         deriving (Show, Eq)

data DataCon = MkDataCon Id [Tm Refined]
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
  MkDefTm :: MHDef -> TopTm Refined

deriving instance (Show) (TopTm a)
deriving instance (Eq) (TopTm a)

data Tm a where
  MkRawId :: Id -> Tm Raw
  MkRawComb :: Id -> [Tm Raw] -> Tm Raw
  MkSC :: SComp a -> Tm a
  MkLet :: Tm a
  MkStr :: String -> Tm a
  MkInt :: Integer -> Tm a
  MkTmSeq :: Tm a -> Tm a -> Tm a
  MkUse :: Use -> Tm Refined
  MkDCon :: DataCon -> Tm Refined

deriving instance (Show) (Tm a)
deriving instance (Eq) (Tm a)

-- A clause for a multihandler definition
data Clause a = MkCls [Pattern] (Tm a)
              deriving (Show, Eq)

data SComp a = MkSComp [Clause a]
           deriving (Show, Eq)

data DataT a = MkDT Id [Id] [Ctr a]
             deriving (Show, Eq)

data Itf a = MkItf Id [Id] [Cmd a]
           deriving (Show, Eq)

data Ctr a = MkCtr Id [VType a]
           deriving (Show, Eq)

data Cmd a = MkCmd Id (CType a)
           deriving (Show, Eq)

data Pattern = MkVPat ValuePat | MkCmdPat Id [ValuePat] Id | MkThkPat Id
             deriving (Show, Eq)

data ValuePat = MkVarPat Id | MkDataPat Id [ValuePat]
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
  MkDTTy :: Id -> Ab a -> [VType a] -> VType a
  MkSCTy :: CType a -> VType a
  MkTVar :: Id -> VType Raw
  MkRTVar :: Id -> VType Refined
  MkFTVar :: Id -> VType Refined
  MkStringTy :: VType a
  MkIntTy :: VType a

deriving instance (Show) (VType a)
deriving instance (Eq) (VType a)

-- Adjustments
data Adj a = MkIdAdj | MkAdjPlus (Adj a) Id [VType a]
           deriving (Show, Eq)

-- Abilities
data Ab a = MkEmpAb | MkAbPlus (Ab a) Id [VType a] | MkOpenAb
          deriving (Show, Eq)
