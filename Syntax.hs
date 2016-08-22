-- The raw abstract syntax and (refined) abstract syntax for Frank
module Syntax where

{-------------------}
{-- The raw syntax as parsed in from the file. --}

data RawProg = MkRawProg [RawTopTm]

-- A raw term collects multihandler signatures and clauses separately.
data RawTopTm = MkRawDataTm DataT | MkRawSigTm MHSig | MkRawDefTm MHCls

-- A top-level multihandler signature and clause
data MHSig = MkSig Id VType
data MHCls = MkMHCls Id Clause

{-------------------}
{-- The (refined) syntax as produced by the pre-processing stage. --}

data Prog = MkProg [TopTm]

-- A top-level term collects multihandler signatures and clauses in one
-- definition.
data TopTm = MkDataT DataT | MkDefTm MHDef

data MHDef = MkDef Id VType [Clause]

{---------------}
{- Parts of the grammar that pre-processing leaves unchanged. -}

data DataT = MkDT Id [Ctr]

data Ctr = MkCtr Id [VType]

-- A clause for a multihandler definition
data Clause = MkCls [Pattern] Tm

data Pattern = MkVPat ValuePat | MkCmdPat | MkThkPat Id
data ValuePat = MkVarPat Id | MkDataPat Id [ValuePat]

data Tm = MkUse Use | MkDCon DataCon | MkSC SComp | MkLet
data SComp = MkSComp [Clause]
data DataCon = MkDataCon Id [Tm]
data Use = MkIdent Id | MkApp Id [Tm]

type Id = String

-- Type hierarchy
data CType = MkCType [Port] Peg
data Port = MkPort Adj VType
data Peg = MkPeg Ab VType
data VType = MkDTTy | MkSCTy CType | MkTVar

-- Adjustments
data Adj = MkIdAdj | MkAdjPlus Adj Id [VType]

-- Abilities
data Ab = MkEmpAb | MkAbPlus Ab Id [VType] | MkOpenAb
