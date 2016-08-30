module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import Syntax

type Refine = ExceptT String (State RState)

data RState = MkRState { interfaces :: [Id]
                       , datatypes :: [Id]
                       , handlers :: [Id]
                       , ctrs :: [Id]
                       , cmds :: [Id]
                       , program :: Prog}

getRState :: Refine RState
getRState = get

putRState :: RState -> Refine ()
putRState = put

putItfs :: [Id] -> Refine ()
putItfs xs = do s <- getRState
                putRState $ s { interfaces = xs }

getItfs :: [RawTopTm] -> [Itf] -> [Itf]
getItfs ((MkRawItfTm itf) : xs) ys = getItfs xs (itf : ys)
getItfs (_ : xs) ys = getItfs xs ys
getItfs [] ys = ys

collectINames :: [Itf] -> [Id]
collectINames ((MkItf itf _ _) : xs) = itf : (collectINames xs)
collectINames [] = []

collectCmds :: [Cmd] -> [Id]
collectCmds ((MkCmd cmd _) : xs) = cmd : (collectCmds xs)
collectCmds [] = []

getDataTs :: [RawTopTm] -> [DataT] -> [DataT]
getDataTs ((MkRawDataTm dt) : xs) ys = getDataTs xs (dt : ys)
getDataTs (_ : xs) ys = getDataTs xs ys
getDataTs [] ys = ys

collectDTNames :: [DataT] -> [Id]
collectDTNames ((MkDT dt _) : xs) = dt : (collectDTNames xs)
collectDTNames [] = []

collectCtrs :: [Ctr] -> [Id]
collectCtrs ((MkCtr ctr _) : xs) = ctr : (collectCtrs xs)
collectCtrs [] = []

getHdrSigs :: [RawTopTm] -> [MHSig] -> [MHSig]
getHdrSigs ((MkRawSigTm sig) : xs) ys = getHdrSigs xs (sig : ys)
getHdrSigs (_ : xs) ys = getHdrSigs xs ys
getHdrSigs [] ys = ys

getHdrDefs :: [RawTopTm] -> [MHCls] -> [MHCls]
getHdrDefs ((MkRawDefTm def) : xs) ys = getHdrDefs xs (def : ys)
getHdrDefs (_ : xs) ys = getHdrDefs xs ys
getHdrDefs [] ys = ys

-- Add the name if not already present
addName :: [Id] -> Id -> Either String [Id]
addName xs x = if x `elem` xs then Left (show x ++ " already defined in " ++
                                         (show xs))
               else Right (x : xs)

refine :: RawProg -> Either String Prog
refine prog = evalState (runExceptT (refine' prog)) initRefine

refine' :: RawProg -> Refine Prog
refine' prog = do i <- getRState
                  return $ program i

{-- The initial state for the refinement pass. -}

builtinCmds :: [Id]
builtinCmds = ["putStrLn", "strcat"]

builtinItfs :: [Id]
builtinItfs = ["Console"]

initRefine :: RState
initRefine = MkRState builtinItfs [] [] [] builtinCmds (MkProg [])
