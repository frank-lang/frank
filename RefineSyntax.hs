{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.List
import qualified Data.Map as M

import Syntax

type Refine = ExceptT String (State RState)

type TVarMap = M.Map Id (VType Raw)

data TopLevelCtxt = Interface | Datatype | Handler deriving (Show, Eq)

data RState = MkRState { interfaces :: [Id]
                       , datatypes :: [Id]
                       , handlers :: [Id]
                       , ctrs :: [Id]
                       , cmds :: [Id]
                       , program :: Prog Refined
                       , tmap :: TVarMap
                       , tlctxt :: Maybe TopLevelCtxt }

getRState :: Refine RState
getRState = get

putRState :: RState -> Refine ()
putRState = put

putRItfs :: [Id] -> Refine ()
putRItfs xs = do s <- getRState
                 putRState $ s { interfaces = xs }

getRItfs :: Refine [Id]
getRItfs = do s <- getRState
              return $ interfaces s

putRDTs :: [Id] -> Refine ()
putRDTs xs = do s <- getRState
                putRState $ s { datatypes = xs }

getRDTs :: Refine [Id]
getRDTs = do s <- getRState
             return $ datatypes s

putRCtrs :: [Id] -> Refine ()
putRCtrs xs = do s <- getRState
                 putRState $ s { ctrs = xs }

getRCtrs :: Refine [Id]
getRCtrs = do s <- getRState
              return $ ctrs s

putRCmds :: [Id] -> Refine ()
putRCmds xs = do s <- getRState
                 putRState $ s { cmds = xs }

getRCmds :: Refine [Id]
getRCmds = do s <- getRState
              return $ cmds s

putRMHs :: [Id] -> Refine ()
putRMHs xs = do s <- getRState
                putRState $ s { handlers = xs }

getRMHs :: Refine [Id]
getRMHs = do s <- getRState
             return $ handlers s

putTMap :: TVarMap -> Refine ()
putTMap m = do s <- getRState
               putRState $ s { tmap = m }

getTMap :: Refine TVarMap
getTMap = do s <- getRState
             return $ tmap s

getTopLevelCtxt :: Refine (Maybe TopLevelCtxt)
getTopLevelCtxt = do s <- getRState
                     return $ tlctxt s

putTopLevelCtxt :: TopLevelCtxt -> Refine ()
putTopLevelCtxt ctxt = do s <- getRState
                          putRState $ s { tlctxt = Just ctxt }

getItfs :: [TopTm Raw] -> [Itf Raw]
getItfs xs = getItfs' xs []
  where getItfs' :: [TopTm Raw] -> [Itf Raw] -> [Itf Raw]
        getItfs' ((MkItfTm itf) : xs) ys = getItfs' xs (itf : ys)
        getItfs' (_ : xs) ys = getItfs' xs ys
        getItfs' [] ys = ys

collectINames :: [Itf Raw] -> [Id]
collectINames ((MkItf itf _ _) : xs) = itf : (collectINames xs)
collectINames [] = []

getCmds :: Itf Raw -> [Cmd Raw]
getCmds (MkItf _ _ xs) = xs

collectCmds :: [Cmd Raw] -> [Id]
collectCmds ((MkCmd cmd _) : xs) = cmd : (collectCmds xs)
collectCmds [] = []

getDataTs :: [TopTm Raw] -> [DataT Raw]
getDataTs xs = getDataTs' xs []
  where getDataTs' :: [TopTm Raw] -> [DataT Raw] -> [DataT Raw]
        getDataTs' ((MkDataTm dt) : xs) ys = getDataTs' xs (dt : ys)
        getDataTs' (_ : xs) ys = getDataTs' xs ys
        getDataTs' [] ys = ys

collectDTNames :: [DataT Raw] -> [Id]
collectDTNames ((MkDT dt _ _) : xs) = dt : (collectDTNames xs)
collectDTNames [] = []

getCtrs :: DataT Raw -> [Ctr Raw]
getCtrs (MkDT _ _ xs) = xs

collectCtrs :: [Ctr Raw] -> [Id]
collectCtrs ((MkCtr ctr _) : xs) = ctr : (collectCtrs xs)
collectCtrs [] = []

getHdrSigs :: [TopTm Raw] -> [MHSig]
getHdrSigs xs = getHdrSigs' xs []
  where getHdrSigs' :: [TopTm Raw] -> [MHSig] -> [MHSig]
        getHdrSigs' ((MkSigTm sig) : xs) ys = getHdrSigs' xs (sig : ys)
        getHdrSigs' (_ : xs) ys = getHdrSigs' xs ys
        getHdrSigs' [] ys = ys

collectMHNames :: [MHSig] -> [Id]
collectMHNames ((MkSig hdr _) : xs) = hdr : (collectMHNames xs)
collectMHNames [] = []

getHdrDefs :: [TopTm Raw] -> [MHCls] -> [MHCls]
getHdrDefs ((MkClsTm cls) : xs) ys = getHdrDefs xs (cls : ys)
getHdrDefs (_ : xs) ys = getHdrDefs xs ys
getHdrDefs [] ys = ys

splitTopTm :: [TopTm Raw] -> ([MHSig], [MHCls], [DataT Raw], [Itf Raw])
splitTopTm xs = (getHdrSigs xs, getHdrDefs xs [], dts, itfs)
  where dts = getDataTs xs
        itfs = getItfs xs

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

uniqueIds :: [Id] -> Bool
uniqueIds xs = length xs == length (nub xs)

isHdrCtxt :: Maybe TopLevelCtxt -> Bool
isHdrCtxt (Just Handler) = True
isHdrCtxt _ = False

refine :: Prog Raw -> Either String (Prog Refined)
refine prog = evalState (runExceptT (refine' prog)) initRefine

refine' :: Prog Raw -> Refine (Prog Refined)
refine' (MkProg xs) = do initialiseRState xs
                         let (sigs, defs, dts, itfs) = splitTopTm xs
                         putTopLevelCtxt Datatype
                         dtTms <- mapM refineDataT dts
                         putTopLevelCtxt Interface
                         itfTms <- mapM refineItf itfs
                         putTopLevelCtxt Handler
                         hdrs <- mapM (refineMH defs) sigs
                         return $ MkProg (dtTms ++ itfTms ++ hdrs)

refineDataT :: DataT Raw -> Refine (TopTm Refined)
refineDataT (MkDT dt ps ctrs) =
  if uniqueIds ps then do putTMap (M.fromList $ zip ps (map MkTVar ps))
                          ctrs' <- mapM refineCtr ctrs
                          putTMap M.empty
                          return $ MkDataTm $ MkDT dt ps ctrs'
  else throwError $ "duplicate parameter in datatype " ++ dt

refineItf :: Itf Raw -> Refine (TopTm Refined)
refineItf (MkItf itf ps cmds) =
  if uniqueIds ps then do putTMap (M.fromList $ zip ps (map MkTVar ps))
                          cmds' <- mapM refineCmd cmds
                          putTMap M.empty
                          return $ MkItfTm $ MkItf itf ps cmds'
  else throwError $ "duplicate parameter in interface " ++ itf

refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd (MkCmd id ty) = do ty' <- refineCType ty
                             return $ MkCmd id ty'

refineCtr :: Ctr Raw -> Refine (Ctr Refined)
refineCtr (MkCtr id xs) = do xs' <- mapM refineVType xs
                             return $ MkCtr id xs'

refineCType :: CType Raw -> Refine (CType Refined)
refineCType (MkCType xs z) = do ys <- mapM refinePort xs
                                peg <- refinePeg z
                                return $ MkCType ys peg

refinePort :: Port Raw -> Refine (Port Refined)
refinePort (MkPort adj ty) = do adj' <- refineAdj adj
                                ty' <- refineVType ty
                                return $ MkPort adj' ty'

refinePeg :: Peg Raw -> Refine (Peg Refined)
refinePeg (MkPeg ab ty) = do ab' <- refineAb ab
                             ty' <- refineVType ty
                             return $ MkPeg ab' ty'

refineAb :: Ab Raw -> Refine (Ab Refined)
refineAb MkEmpAb = return MkEmpAb
refineAb (MkAbPlus ab id xs) = do xs' <- mapM refineVType xs
                                  ab' <- refineAb ab
                                  return $ MkAbPlus ab' id xs'
refineAb MkOpenAb = return MkOpenAb


refineAdj :: Adj Raw -> Refine (Adj Refined)
refineAdj (MkAdjPlus adj id xs) = do xs' <- mapM refineVType xs
                                     adj' <- refineAdj adj
                                     return $ MkAdjPlus adj' id xs'
refineAdj MkIdAdj = return MkIdAdj

refineVType :: VType Raw -> Refine (VType Refined)
-- Check that dt is a datatype, otherwise it must have been a type variable.
refineVType (MkDTTy x ab xs) =
  do dts <- getRDTs
     case x `elem` dts of
       True -> do ab' <- refineAb ab
                  xs' <- mapM refineVType xs
                  return $ MkDTTy x ab' xs'
       False -> do -- interfaces or datatypes explicitly declare their type
                   -- variables.
                   m <- getTMap
                   ctx <- getTopLevelCtxt
                   if isHdrCtxt ctx || M.member x m then return $ MkTVar x
                   else throwError $ "no type variable " ++ x ++ " defined"
refineVType (MkSCTy ty) = refineCType ty >>= return . MkSCTy
refineVType (MkTVar id) = return $ MkTVar id
refineVType MkStringTy = return MkStringTy
refineVType MkIntTy = return MkIntTy

refineMH :: [MHCls] -> MHSig -> Refine (TopTm Refined)
refineMH xs (MkSig id ty) = do cs <- mapM refineMHCls ys
                               ty' <- refineCType ty
                               return $ MkDefTm $ MkDef id ty' cs
  where ys = filter (\(MkMHCls id' _) -> id' == id) xs

refineMHCls :: MHCls -> Refine (Clause Refined)
refineMHCls (MkMHCls _ (MkCls ps tm)) = do tm' <- refineTm tm
                                           return $ MkCls ps tm'

refineTm :: Tm Raw -> Refine (Tm Refined)
refineTm (MkRawId id) =
  do cmds <- getRCmds
     hdrs <- getRMHs
     if id `elem` cmds then return $ MkUse $ MkOp $ MkCmdId id
     else if id `elem` hdrs then return $ MkUse $ MkOp $ MkPoly id
     else return $ MkUse $ MkOp $ MkMono id
refineTm (MkRawComb id xs) =
  do xs' <- mapM refineTm xs
     ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     if id `elem` ctrs then return $ MkDCon $ MkDataCon id xs'
     else if id `elem` cmds then return $ MkUse $ MkApp (MkCmdId id) xs'
     else if id `elem` hdrs then return $ MkUse $ MkApp (MkPoly id) xs'
     else return $ MkUse $ MkApp (MkMono id) xs'
refineTm (MkSC x) = do x' <- refineSComp x
                       return $ MkSC x'
refineTm (MkStr x) = return $ MkStr x
refineTm (MkInt x) = return $ MkInt x
refineTm (MkTmSeq t1 t2) = do t1' <- refineTm t1
                              t2' <- refineTm t2
                              return $ MkTmSeq t1' t2'

refineSComp :: SComp Raw -> Refine (SComp Refined)
refineSComp (MkSComp xs) = do xs' <- mapM refineClause xs
                              return $ MkSComp xs'

refineClause :: Clause Raw -> Refine (Clause Refined)
refineClause (MkCls ps tm) = do tm' <- refineTm tm
                                return $ MkCls ps tm'

initialiseRState :: [TopTm Raw] -> Refine ()
initialiseRState xs =
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
builtinCmds = ["putStrLn"]

builtinMHs :: [Id]
builtinMHs = ["strcat"]

builtinItfs :: [Id]
builtinItfs = ["Console"]

builtinDataTs :: [Id]
builtinDataTs = ["Unit"]

initRefine :: RState
initRefine = MkRState builtinItfs builtinDataTs builtinMHs [] builtinCmds
             (MkProg []) M.empty Nothing
