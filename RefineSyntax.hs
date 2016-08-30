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

putRItfs :: [Id] -> Refine ()
putRItfs xs = do s <- getRState
                 putRState $ s { interfaces = xs }

putRDTs :: [Id] -> Refine ()
putRDTs xs = do s <- getRState
                putRState $ s { datatypes = xs }

putRCtrs :: [Id] -> Refine ()
putRCtrs xs = do s <- getRState
                 putRState $ s { ctrs = xs }

putRCmds :: [Id] -> Refine ()
putRCmds xs = do s <- getRState
                 putRState $ s { cmds = xs }

putRMHs :: [Id] -> Refine ()
putRMHs xs = do s <- getRState
                putRState $ s { handlers = xs }

getItfs :: [RawTopTm] -> [Itf]
getItfs xs = getItfs' xs []
  where getItfs' :: [RawTopTm] -> [Itf] -> [Itf]
        getItfs' ((MkRawItfTm itf) : xs) ys = getItfs' xs (itf : ys)
        getItfs' (_ : xs) ys = getItfs' xs ys
        getItfs' [] ys = ys

collectINames :: [Itf] -> [Id]
collectINames ((MkItf itf _ _) : xs) = itf : (collectINames xs)
collectINames [] = []

getCmds :: Itf -> [Cmd]
getCmds (MkItf _ _ xs) = xs

collectCmds :: [Cmd] -> [Id]
collectCmds ((MkCmd cmd _) : xs) = cmd : (collectCmds xs)
collectCmds [] = []

getDataTs :: [RawTopTm] -> [DataT]
getDataTs xs = getDataTs' xs []
  where getDataTs' :: [RawTopTm] -> [DataT] -> [DataT]
        getDataTs' ((MkRawDataTm dt) : xs) ys = getDataTs' xs (dt : ys)
        getDataTs' (_ : xs) ys = getDataTs' xs ys
        getDataTs' [] ys = ys

collectDTNames :: [DataT] -> [Id]
collectDTNames ((MkDT dt _) : xs) = dt : (collectDTNames xs)
collectDTNames [] = []

getCtrs :: DataT -> [Ctr]
getCtrs (MkDT _ xs) = xs

collectCtrs :: [Ctr] -> [Id]
collectCtrs ((MkCtr ctr _) : xs) = ctr : (collectCtrs xs)
collectCtrs [] = []

getHdrSigs :: [RawTopTm] -> [MHSig]
getHdrSigs xs = getHdrSigs' xs []
  where getHdrSigs' :: [RawTopTm] -> [MHSig] -> [MHSig]
        getHdrSigs' ((MkRawSigTm sig) : xs) ys = getHdrSigs' xs (sig : ys)
        getHdrSigs' (_ : xs) ys = getHdrSigs' xs ys
        getHdrSigs' [] ys = ys

collectMHNames :: [MHSig] -> [Id]
collectMHNames ((MkSig hdr _) : xs) = hdr : (collectMHNames xs)
collectMHNames [] = []

getHdrDefs :: [RawTopTm] -> [MHCls] -> [MHCls]
getHdrDefs ((MkRawDefTm def) : xs) ys = getHdrDefs xs (def : ys)
getHdrDefs (_ : xs) ys = getHdrDefs xs ys
getHdrDefs [] ys = ys

-- Add the name if not already present
addName :: [Id] -> Id -> String -> Refine [Id]
addName xs x prefix = if x `elem` xs then throwError (prefix ++ show x ++
                                                      " already defined.")
                      else return $ x : xs

addItf :: [Id] -> Id -> Refine [Id]
addItf xs x = addName xs x "duplicate interface:"

addDataT :: [Id] -> Id -> Refine [Id]
addDataT xs x = addName xs x "duplicate datatype:"

addCtr :: [Id] -> Id -> Refine [Id]
addCtr xs x = addName xs x "duplicate constructor:"

addCmd :: [Id] -> Id -> Refine [Id]
addCmd xs x = addName xs x "duplicate command:"

addMH :: [Id] -> Id -> Refine [Id]
addMH xs x = addName xs x "duplicate multihandler:"

refine :: RawProg -> Either String Prog
refine prog = evalState (runExceptT (refine' prog)) initRefine

refine' :: RawProg -> Refine Prog
refine' prog = do initialiseRState prog
                  i <- getRState
                  return $ program i

initialiseRState :: RawProg -> Refine ()
initialiseRState (MkRawProg xs) =
  do i <- getRState
     let itfs = getItfs xs
         dts = getDataTs xs
         hdrSigs = getHdrSigs xs
     itfNames <- foldM addItf (interfaces i) (collectINames itfs)
     dtNames <- foldM addDataT (datatypes i) (collectDTNames dts)
     mhNames <- foldM addMH (handlers i) (collectMHNames hdrSigs)
     cmds <- foldM addCmd (cmds i) (collectCmds $ concatMap getCmds itfs)
     ctrs <- foldM addCtr (ctrs i) (collectCtrs $ concatMap getCtrs dts)
     putRItfs itfNames
     putRDTs dtNames
     putRCmds cmds
     putRCtrs ctrs
     putRMHs mhNames

{-- The initial state for the refinement pass. -}

builtinCmds :: [Id]
builtinCmds = ["putStrLn", "strcat"]

builtinItfs :: [Id]
builtinItfs = ["Console"]

initRefine :: RState
initRefine = MkRState builtinItfs [] [] [] builtinCmds (MkProg [])
