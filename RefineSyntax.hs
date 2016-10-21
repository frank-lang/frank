{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax

type Refine = ExceptT String (State RState)

type TVarMap = M.Map Id (VType Raw)

type EVarSet = S.Set Id

data TopLevelCtxt = Interface | Datatype | Handler deriving (Show, Eq)

data RState = MkRState { interfaces :: [Id]
                       , datatypes :: [Id]
                       , handlers :: [Id]
                       , ctrs :: [Id]
                       , cmds :: [Id]
                       , program :: Prog Refined
                       , tmap :: TVarMap
                       , evmap :: EVarSet
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

putEVSet :: EVarSet -> Refine ()
putEVSet m = do s <- getRState
                putRState $ s { evmap = m }

getEVSet :: Refine EVarSet
getEVSet = do s <- getRState
              return $ evmap s

getTopLevelCtxt :: Refine (Maybe TopLevelCtxt)
getTopLevelCtxt = do s <- getRState
                     return $ tlctxt s

putTopLevelCtxt :: TopLevelCtxt -> Refine ()
putTopLevelCtxt ctxt = do s <- getRState
                          putRState $ s { tlctxt = Just ctxt }

collectCmds :: [Cmd a] -> [Id]
collectCmds ((MkCmd cmd _ _) : xs) = cmd : (collectCmds xs)
collectCmds [] = []

collectCtrs :: [Ctr a] -> [Id]
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
addName xs x prefix = if x `elem` xs then throwError (prefix ++ x ++
                                                      " already defined.")
                      else return $ x : xs

addItf :: [Id] -> Id -> Refine [Id]
addItf xs x = addName xs x "duplicate interface: "

addDataT :: [Id] -> Id -> Refine [Id]
addDataT xs x = addName xs x "duplicate datatype: "

addCtr :: [Id] -> Id -> Refine [Id]
addCtr xs x = addName xs x "duplicate constructor: "

addCmd :: [Id] -> Id -> Refine [Id]
addCmd xs x = addName xs x "duplicate command: "

addMH :: [Id] -> Id -> Refine [Id]
addMH xs x = addName xs x "duplicate multihandler: "

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
                         if existsMain hdrs then
                            return $ MkProg (map MkDataTm builtinDataTs ++
                                             dtTms ++
                                             map MkItfTm builtinItfs ++
                                             itfTms ++
                                             map MkDefTm builtinMHDefs ++
                                             hdrs)
                         else throwError $ "no main function defined."

existsMain :: [TopTm Refined] -> Bool
existsMain ((MkDefTm (MkDef id _ _)) : xs) = id == "main" || existsMain xs
existsMain [] = False
existsMain (_ : xs) = error "invalid top term: expected multihandler"

refineDataT :: DataT Raw -> Refine (TopTm Refined)
refineDataT (MkDT dt es ps ctrs) =
  if uniqueIds ps && uniqueIds es then
     do putTMap (M.fromList $ zip ps (map MkTVar ps))
        putEVSet (S.fromList es)
        ctrs' <- mapM refineCtr ctrs
        putTMap M.empty
        putEVSet S.empty
        return $ MkDataTm $ MkDT dt es ps ctrs'
  else throwError $ "duplicate parameter in datatype " ++ dt

refineItf :: Itf Raw -> Refine (TopTm Refined)
refineItf (MkItf itf ps cmds) =
  if uniqueIds ps then do putTMap (M.fromList $ zip ps (map MkTVar ps))
                          cmds' <- mapM refineCmd cmds
                          putTMap M.empty
                          return $ MkItfTm $ MkItf itf ps cmds'
  else throwError $ "duplicate parameter in interface " ++ itf

refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd (MkCmd id xs y) = do xs' <- mapM refineVType xs
                               y' <- refineVType y
                               return $ MkCmd id xs' y'

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
refineAb ab@(MkAb v m) =
  do es <- getEVars $ M.toList m
     if null es then do m' <- refineItfMap m
                        return $ MkAb (refineAbMod v) m'
     else if length es == 1 then do let u = head es
                                    m' <- refineItfMap (M.delete u m)
                                    return $ MkAb (MkAbVar u) m'
     else throwError $ "ability has multiple effect variables " ++ (show es)

getEVars :: [(Id,[VType Raw])] -> Refine [Id]
getEVars ((x,ts) : ys) =
  do p <- getEVSet
     es <- getEVars ys
     if S.member x p then
       if length ts == 0 then return $ x : es
       else throwError $
            "effect variable " ++ x ++ " may not take parameters"
     else return es
getEVars [] = return []

refineItfMap :: ItfMap Raw -> Refine (ItfMap Refined)
refineItfMap m = do xs <- mapM (uncurry refineEntry) (M.toList m)
                    return $ M.fromList xs
  where refineEntry :: Id -> [VType Raw] -> Refine (Id, [VType Refined])
        refineEntry id xs =
          do itfs <- getRItfs
             if id `elem` itfs then do xs' <- mapM refineVType xs
                                       return (id, xs')
             else throwError $ "no such effect variable or interface " ++ id

refineAbMod :: AbMod Raw -> AbMod Refined
refineAbMod MkEmpAb = MkEmpAb
refineAbMod (MkAbVar x) = MkAbVar x

refineAdj :: Adj Raw -> Refine (Adj Refined)
refineAdj (MkAdj m) = do m' <- mapM (mapM refineVType) m
                         return $ MkAdj m'

refineVType :: VType Raw -> Refine (VType Refined)
-- Check that dt is a datatype, otherwise it must have been a type variable.
refineVType (MkDTTy x abs xs) =
  do dts <- getRDTs
     case x `elem` dts of
       True -> do abs' <- mapM refineAb abs
                  xs' <- mapM refineVType xs
                  return $ MkDTTy x abs' xs'
       False -> do -- interfaces or datatypes explicitly declare their type
                   -- variables.
                   m <- getTMap
                   ctx <- getTopLevelCtxt
                   if isHdrCtxt ctx || M.member x m then return $ MkTVar x
                   else throwError $ "no type variable " ++ x ++ " defined"
refineVType (MkSCTy ty) = refineCType ty >>= return . MkSCTy
refineVType (MkTVar x) = do dts <- getRDTs
                            case x `elem` dts of
                              True -> return $ MkDTTy x [] []
                              False -> return $ MkTVar x
refineVType MkStringTy = return MkStringTy
refineVType MkIntTy = return MkIntTy
refineVType MkCharTy = return MkCharTy

refineMH :: [MHCls] -> MHSig -> Refine (TopTm Refined)
refineMH xs (MkSig id ty) = do cs <- mapM refineMHCls ys
                               ty' <- refineCType ty
                               return $ MkDefTm $ MkDef id ty' cs
  where ys = filter (\(MkMHCls id' _) -> id' == id) xs

refineMHCls :: MHCls -> Refine (Clause Refined)
refineMHCls (MkMHCls _ cls) = refineClause cls

refineTm :: Tm Raw -> Refine (Tm Refined)
refineTm (MkRawId id) =
  do ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     if id `elem` ctrs then return $ MkDCon $ MkDataCon id []
     else if id `elem` cmds then return $ MkUse $ MkOp $ MkCmdId id
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
refineTm (MkChar x) = return $ MkChar x
refineTm (MkTmSeq t1 t2) = do t1' <- refineTm t1
                              t2' <- refineTm t2
                              return $ MkTmSeq t1' t2'

refineSComp :: SComp Raw -> Refine (SComp Refined)
refineSComp (MkSComp xs) = do xs' <- mapM refineClause xs
                              return $ MkSComp xs'

refineClause :: Clause Raw -> Refine (Clause Refined)
refineClause (MkCls ps tm) = do ps' <- mapM refinePattern ps
                                tm' <- refineTm tm
                                return $ MkCls ps' tm'

refinePattern :: Pattern -> Refine Pattern
refinePattern (MkVPat p) = MkVPat <$> refineVPat p
refinePattern (MkCmdPat cmd ps k) = do ps' <- mapM refineVPat ps
                                       return $ MkCmdPat cmd ps' k
refinePattern p = return p

refineVPat :: ValuePat -> Refine ValuePat
refineVPat p@(MkVarPat x) =
  do ctrs <- getRCtrs
     if x `elem` ctrs then return $ MkDataPat x []
     else return p
refineVPat p = return p

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

makeIntBinOp :: Char -> MHDef Refined
makeIntBinOp c = MkDef [c] (MkCType [MkPort (MkAdj M.empty) MkIntTy
                                    ,MkPort (MkAdj M.empty) MkIntTy]
                            (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)) []

{-- The initial state for the refinement pass. -}

builtinDataTs :: [DataT Refined]
builtinDataTs = [MkDT "List" [] ["X"] [MkCtr "cons" [MkTVar "X"
                                                    ,MkDTTy "List" []
                                                     [MkTVar "X"]]
                                      ,MkCtr "nil" []]
                ,MkDT "Unit" [] [] [MkCtr "unit" []]]


builtinItfs :: [Itf Refined]
builtinItfs = [MkItf "Console" [] [MkCmd "putStrLn" [MkStringTy]
                                   (MkDTTy "Unit" [] [])
                                  ,MkCmd "getStr" [] MkStringTy]
              ,MkItf "CursesConsole" [] [MkCmd "inch" [] MkCharTy
                                        ,MkCmd "ouch" [MkCharTy]
                                         (MkDTTy "Unit" [] [])]]

builtinMHDefs :: [MHDef Refined]
builtinMHDefs = [MkDef "strcat"
                 (MkCType [MkPort (MkAdj M.empty) MkStringTy
                          ,MkPort (MkAdj M.empty) MkStringTy]
                  (MkPeg (MkAb (MkAbVar "£") M.empty) MkStringTy)) []] ++
                (map makeIntBinOp "+-")

builtinMHs :: [Id]
builtinMHs = map (\(MkDef id _ _) -> id) builtinMHDefs

builtinDTs :: [Id]
builtinDTs = collectDTNames builtinDataTs

builtinINames :: [Id]
builtinINames = collectINames builtinItfs

builtinCtrs :: [Id]
builtinCtrs = map (\(MkCtr id _) -> id) $ concatMap getCtrs builtinDataTs

builtinCmds :: [Id]
builtinCmds = map (\(MkCmd id _ _) -> id) $ concatMap getCmds builtinItfs

initRefine :: RState
initRefine = MkRState builtinINames builtinDTs builtinMHs builtinCtrs
             builtinCmds (MkProg []) M.empty S.empty Nothing
