module RefineSyntax where

import Syntax

-- Some type synonyms for code commentary
type EffectItfs = [RawTopTm]
type DataTCol = [RawTopTm]
type MHSigCol = [RawTopTm]
type MHDefCol = [RawTopTm]

type CtrCol = [Id]
type CmdCol = [Id]

refine :: RawProg -> Prog
refine prog = runRefinement prog

getItfs :: [RawTopTm] -> EffectItfs -> EffectItfs
getItfs ((MkRawItfTm itf) : xs) ys = getItfs xs (itf : ys)
getItfs (_ : xs) ys = getItfs xs ys
getItfs [] ys = ys

getDataTs :: [RawTopTm] -> DataTCol -> DataTCol
getDataTs ((MkRawDataTm dt) : xs) ys = getDataTs xs (dt : ys)
getDataTs (_ : xs) ys = getDataTs xs ys
getDataTs [] ys = ys

getHdrSigs :: [RawTopTm] -> MHSigCol -> MHSigCol
getHdrSigs ((MkRawSigTm sig) : xs) ys = getHdrSigs xs (sig : ys)
getHdrSigs (_ : xs) ys = getHdrSigs xs ys
getHdrSigs [] ys = ys

getHdrDefs :: [RawTopTm] -> MHDefCol -> MHDefCol
getHdrDefs ((MkRawDefTm def) : xs) ys = getHdrDefs xs (def : ys)
getHdrDefs (_ : xs) ys = getHdrDefs xs ys
getHdrDefs [] ys = ys

refine' :: CtrNames -> CmdNames -> MHNames -> RawProg -> Prog
refine' cs cmds mhs prog = MkProg

refineClause :: RawClause -> Clause
