-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

{-------------------}
{-- The raw syntax as parsed in from the file. --}

data RawProg = MkRawProg [RawTopTm]
             deriving (Show, Eq)

-- A raw term collects multihandler signatures and clauses separately.
data RawTopTm = MkRawDataTm DataT | MkRawSigTm MHSig | MkRawDefTm MHCls
              deriving (Show, Eq)

-- A top-level multihandler signature and clause
data MHSig = MkSig Id CType
           deriving (Show, Eq)

data MHCls = MkMHCls Id Clause
           deriving (Show, Eq)

{-------------------}
{-- The (refined) syntax as produced by the pre-processing stage. --}

data Prog = MkProg [TopTm]
          deriving (Show, Eq)

-- A top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTm = MkDataT DataT | MkDefTm MHDef
           deriving (Show, Eq)

data MHDef = MkDef Id VType [Clause]
           deriving (Show, Eq)
{---------------}
{- Parts of the grammar that pre-processing leaves unchanged. -}

data DataT = MkDT Id [Ctr]
           deriving (Show, Eq)

data Ctr = MkCtr Id [VType]
         deriving (Show, Eq)

-- A clause for a multihandler definition
data Clause = MkCls [Pattern] Tm
            deriving (Show, Eq)

data Pattern = MkVPat ValuePat | MkCmdPat | MkThkPat Id
             deriving (Show, Eq)

data ValuePat = MkVarPat Id | MkDataPat Id [ValuePat]
              deriving (Show, Eq)

data Tm = MkUse Use | MkDCon DataCon | MkSC SComp | MkLet
        deriving (Show, Eq)

data SComp = MkSComp [Clause]
           deriving (Show, Eq)

data DataCon = MkDataCon Id [Tm]
             deriving (Show, Eq)

data Use = MkIdent Id | MkApp Id [Tm]
         deriving (Show, Eq)

type Id = String

-- Type hierarchy
data CType = MkCType [Port] Peg
           deriving (Show, Eq)

data Port = MkPort Adj VType
          deriving (Show, Eq)

data Peg = MkPeg Ab VType
         deriving (Show, Eq)

data VType = MkDTTy | MkSCTy CType | MkTVar Id
           deriving (Show, Eq)

-- Adjustments
data Adj = MkIdAdj | MkAdjPlus Adj Id [VType]
         deriving (Show, Eq)

-- Abilities
data Ab = MkEmpAb | MkAbPlus Ab Id [VType] | MkOpenAb
        deriving (Show, Eq)
