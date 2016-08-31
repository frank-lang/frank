-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

{-------------------}
{-- The raw syntax as parsed in from the file. --}

data RawProg = MkRawProg [RawTopTm]
             deriving (Show, Read, Eq)

-- A raw term collects multihandler signatures and clauses separately.
data RawTopTm = MkRawDataTm DataT | MkRawSigTm MHSig | MkRawDefTm MHCls
              | MkRawItfTm Itf
              deriving (Show, Read, Eq)

-- A top-level multihandler signature and clause
data MHSig = MkSig Id CType
           deriving (Show, Read, Eq)

data MHCls = MkMHCls Id RawClause
           deriving (Show, Read, Eq)

data RawClause = MkRawCls [Pattern] RawTm
               deriving (Show, Read, Eq)

data RawTm = MkRawId Id | MkRawComb Id [RawTm] | MkRawSC RawSComp | MkRawLet
           | MkRawStr String | MkRawInt Integer | MkRawTmSeq RawTm RawTm
           deriving (Show, Read, Eq)

data RawSComp = MkRawSComp [RawClause]
              deriving (Show, Read, Eq)
{-------------------}
{-- The (refined) syntax as produced by the pre-processing stage. --}

data Prog = MkProg [TopTm]
          deriving (Show, Read, Eq)

-- A top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTm = MkDataT DataT | MkDefTm MHDef
           deriving (Show, Read, Eq)

data MHDef = MkDef Id VType [Clause]
           deriving (Show, Read, Eq)

-- A clause for a multihandler definition
data Clause = MkCls [Pattern] Tm
            deriving (Show, Read, Eq)

data Tm = MkUse Use | MkDCon DataCon | MkSC SComp | MkLet
        deriving (Show, Read, Eq)

data Use = MkIdent Id | MkApp Id [Tm]
         deriving (Show, Read, Eq)

data SComp = MkSComp [Clause]
           deriving (Show, Read, Eq)
{---------------}
{- Parts of the grammar that pre-processing leaves unchanged. -}

data DataT = MkDT Id [Id] [Ctr]
           deriving (Show, Read, Eq)

data Itf = MkItf Id [Id] [Cmd]
         deriving (Show, Read, Eq)

data Ctr = MkCtr Id [VType]
         deriving (Show, Read, Eq)

data Cmd = MkCmd Id CType
         deriving (Show, Read, Eq)

data Pattern = MkVPat ValuePat | MkCmdPat Id [ValuePat] Id | MkThkPat Id
             deriving (Show, Read, Eq)

data ValuePat = MkVarPat Id | MkDataPat Id [ValuePat]
              deriving (Show, Read, Eq)

data DataCon = MkDataCon Id [Tm]
             deriving (Show, Read, Eq)

type Id = String

-- Type hierarchy
data CType = MkCType [Port] Peg
           deriving (Show, Read, Eq)

data Port = MkPort Adj VType
          deriving (Show, Read, Eq)

data Peg = MkPeg Ab VType
         deriving (Show, Read, Eq)

data VType = MkDTTy Id Ab [VType] | MkSCTy CType
           | MkTVar Id | MkStringTy | MkIntTy
           deriving (Show, Read, Eq)

-- Adjustments
data Adj = MkIdAdj | MkAdjPlus Adj Id [VType]
         deriving (Show, Read, Eq)

-- Abilities
data Ab = MkEmpAb | MkAbPlus Ab Id [VType] | MkOpenAb
        deriving (Show, Read, Eq)
