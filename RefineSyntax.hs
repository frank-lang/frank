{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State

import Debug.Trace

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax

type Refine = ExceptT String (State RState)

type TVarMap = M.Map Id (VType Raw)

type EVarSet = S.Set Id

-- Object-Int pair
type IPair = (Id,Int)
-- data type id is mapped to rigid data type (RDT) variables (for polymorphic data types)
type DTMap = M.Map Id [(Id, Kind)]
type IFMap = M.Map Id [(Id, Kind)]

data TopLevelCtxt = Interface | Datatype | Handler
  deriving (Show, Eq)

data RState = MkRState { interfaces :: IFMap     -- Id -> [(Id, Kind)]       store type & effect variables of each interface
                       , datatypes :: DTMap      -- Id -> [(Id, Kind)]       store type & effect variables of each data type
                       , handlers :: [IPair]     -- handler Id -> # of arguments
                       , ctrs :: [IPair]         -- constructor Id -> # of arguments
                       , cmds :: [IPair]         -- command Id -> # of arguments
                       , program :: Prog Refined -- LC: what is this for?
                       , tmap :: TVarMap         -- type var Id ->   VType Raw     type vars of current context
                       , evmap :: EVarSet        -- effect var Id                  effect vars of current context
                       , tlctxt :: Maybe TopLevelCtxt }

getRState :: Refine RState
getRState = get

putRState :: RState -> Refine ()
putRState = put

putRItfs :: IFMap -> Refine ()
putRItfs xs = do s <- getRState
                 putRState $ s { interfaces = xs }

getRItfs :: Refine IFMap
getRItfs = do s <- getRState
              return $ interfaces s

putRDTs :: DTMap -> Refine ()
putRDTs m = do s <- getRState
               putRState $ s { datatypes = m }

-- get rigid data types
getRDTs :: Refine DTMap
getRDTs = do s <- getRState
             return $ datatypes s

putRCtrs :: [IPair] -> Refine ()
putRCtrs xs = do s <- getRState
                 putRState $ s { ctrs = xs }

getRCtrs :: Refine [IPair]
getRCtrs = do s <- getRState
              return $ ctrs s

putRCmds :: [IPair] -> Refine ()
putRCmds xs = do s <- getRState
                 putRState $ s { cmds = xs }

getRCmds :: Refine [IPair]
getRCmds = do s <- getRState
              return $ cmds s

putRMHs :: [IPair] -> Refine ()
putRMHs xs = do s <- getRState
                putRState $ s { handlers = xs }

getRMHs :: Refine [IPair]
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

mem :: Id -> [IPair] -> Bool
mem x xs = x `elem` (map fst xs)

findPair :: Id -> [IPair] -> Maybe Int
findPair x ((y,n) : xs) = if x == y then Just n else findPair x xs
findPair _ _ = Nothing

collectCmds :: [Cmd a] -> [Id]
collectCmds ((MkCmd cmd _ _ _) : xs) = cmd : (collectCmds xs)
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
getHdrDefs [] ys = reverse ys

splitTopTm :: [TopTm Raw] -> ([MHSig], [MHCls], [DataT Raw], [Itf Raw])
splitTopTm xs = (getHdrSigs xs, getHdrDefs xs [], dts, itfs)
  where dts = getDataTs xs
        itfs = getItfs xs

-- Add the name if not already present
addEntry :: [IPair] -> Id -> Int -> String -> Refine [IPair]
addEntry xs x n prefix = if x `mem` xs then throwError (prefix ++ x ++
                                                        " already defined.")
                         else return $ (x,n) : xs

-- addItf :: [IPair] -> Itf a -> Refine [IPair]
-- addItf xs (MkItf x ps _) = addEntry xs x (length ps) "duplicate interface: "

addItf :: IFMap -> Itf a -> Refine DTMap
addItf m (MkItf x ps _) = if M.member x m then
                             throwError ("duplicate interface: " ++ x ++
                                          " already defined.")
                           else return $ M.insert x ps m


addDataT :: DTMap -> DataT a -> Refine DTMap
addDataT m (MkDT x ps _) = if M.member x m then
                             throwError ("duplicate datatype: " ++ x ++
                                          " already defined.")
                           else return $ M.insert x ps m

addCtr :: [IPair] -> Ctr a -> Refine [IPair]
addCtr xs (MkCtr x ts) = addEntry xs x (length ts) "duplicate constructor: "

addCmd :: [IPair] -> Cmd a -> Refine [IPair]
addCmd xs (MkCmd x _ ts _) = addEntry xs x (length ts) "duplicate command: "

-- takes map handler-id -> #-of-ports and adds another handler entry
addMH :: [IPair] -> MHSig -> Refine [IPair]
addMH xs (MkSig x (MkCType ps p)) =
  addEntry xs x (length ps) "duplicate multihandler: "

uniqueIds :: [Id] -> Bool
uniqueIds xs = length xs == length (nub xs)

isHdrCtxt :: Maybe TopLevelCtxt -> Bool
isHdrCtxt (Just Handler) = True
isHdrCtxt _ = False

refine :: Prog Raw -> Either String (Prog Refined)
refine prog = evalState (runExceptT (refine' prog)) initRefine

-- explicit refinements:
-- + check if main function exists
-- + built-in data types, interfaces, operators are added
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

-- explicit refinements:
-- + data type has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineDataT :: DataT Raw -> Refine (TopTm Refined)
refineDataT d@(MkDT dt ps           ctrs) =
--          data dt p_1 ... p_m = ctr_1 | ... | ctr_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- add [£] if any constructor's arg. ty contains implicit [£]
       let (evs', ps') = if not (any ((==) "£") evs) && polyDataT d then
                            (evs ++ ["£"], ps ++ [("£", ET)])
                         else (evs, ps)
       -- add new rigid data type
       m <- getRDTs
       putRDTs $ M.insert dt ps' m
       -- refine constructors
       putTMap (M.fromList $ zip tvs (map MkTVar tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs')                      -- temp. eff ty vars
       ctrs' <- mapM refineCtr ctrs
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ MkDataTm $ MkDT dt ps' ctrs'
  else throwError $ "duplicate parameter in datatype " ++ dt

-- explicit refinements:
-- + interface has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineItf :: Itf Raw -> Refine (TopTm Refined)
refineItf i@(MkItf itf ps      cmds) =
--        interface itf p_1 ... p_m = cmd_1 | ... | cmd_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- add [£] if any command's arg. ty contains implicit [£]
       let (evs', ps') = if not (any ((==) "£") evs) && polyItf i then
                            (evs ++ ["£"], ps ++ [("£", ET)])
                         else (evs, ps)
       -- add new rigid interface
       m <- getRItfs
       putRItfs $ M.insert itf ps' m
       -- refine commands
       putTMap (M.fromList $ zip tvs (map MkTVar tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs')                      -- temp. eff ty vars
       cmds' <- mapM refineCmd cmds
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ MkItfTm $ MkItf itf ps' cmds'
  else throwError $ "duplicate parameter in interface " ++ itf

-- explicit refinements:
-- + command has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd c@(MkCmd id ps xs y) =
--        id : forall p_1 ... p_m, x_1 -> ... -> x_n -> y
  if uniqueIds (map fst ps) then
    do tmap <- getTMap
       evset <- getEVSet
       -- check that none of this cmd's ty vars coincide with the itf's ones
       if uniqueIds (map fst ps ++ map fst (M.toList tmap) ++ S.toList evset) then
         do
           let tvs = [x | (x, VT) <- ps] -- val ty vars
           let evs = [x | (x, ET) <- ps] -- eff ty vars
           -- add [£] if any constructor's arg. ty contains implicit [£]
           let (evs', ps') = if not (any ((==) "£") evs) && polyCmd c then
                                (evs ++ ["£"], ps ++ [("£", ET)])
                             else (evs, ps)
           -- refine argument types and result type
           -- first add temp. val, eff ty vars
           putTMap (M.union tmap (M.fromList $ zip tvs (map MkTVar tvs)))
           putEVSet (S.union evset (S.fromList evs))
           -- refine
           xs' <- mapM refineVType xs
           y' <- refineVType y
           -- reset temp val, eff ty vars
           putTMap tmap
           putEVSet evset
           return $ MkCmd id ps xs' y'
       else throwError $ "a type parameter of command " ++ id ++
                         "already occurs as interface type parameter"
  else throwError $ "duplicate parameter in command " ++ id


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

getEVars :: [(Id,[TyArg Raw])] -> Refine [Id]
getEVars ((x, ts) : ys) =
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
  where refineEntry :: Id -> [TyArg Raw] -> Refine (Id, [TyArg Refined])
        refineEntry x ts =
          do itfs <- getRItfs
             case M.lookup x itfs of
               Just ps ->
                 do let ts' = if length ps == length ts + 1 &&
                                 (snd (ps !! length ts) == ET) then
                                ts ++ [EArg (MkAb (MkAbVar "£") M.empty)]
                              else
                                ts
                    checkArgs x (length ps) (length ts')
                    ts'' <- mapM refineTyArg ts'
                    return (x, ts'')
               Nothing -> idError x "interface"

refineAbMod :: AbMod Raw -> AbMod Refined
refineAbMod MkEmpAb = MkEmpAb
refineAbMod (MkAbVar x) = MkAbVar x

refineAdj :: Adj Raw -> Refine (Adj Refined)
refineAdj (MkAdj m) = do m' <- refineItfMap m
                         return $ MkAdj m'

-- explicit refinements:
-- + implicit [£] ty args to data types are made explicit
-- + MkDTTy is distinguished between being
--   1) data type indeed  -> MkDTTy
--   2) introduced ty var -> MkTVar
--      TODO: LC: shouldn't there be an error as type constructors can't occur as MkTVar's?
-- + MkTVar is distinguished between being
--   1) data type         -> MkDTTy
--   2) introduced ty var -> MkTVar
-- + ty arguments refer only to introduced val tys
refineVType :: VType Raw -> Refine (VType Refined)
refineVType (MkDTTy x  ts) =
--           x t_1 ... t_n
  do dtm <- getRDTs
     case M.lookup x dtm of
       Just ps ->
--        1) data x p_1 ... p_n
--    or  2) data x p_1 ... p_n [£]       ([£] has been explicitly added during ref't)
         do           -- If 2), set t_{n+1} := [£]
            let ts' = if length ps == length ts + 1 && (snd (ps !! length ts) == ET) then
                        ts ++ [EArg (MkAb (MkAbVar "£") M.empty)]
                      else
                        ts
            checkArgs x (length ps) (length ts')
            ts'' <- mapM refineTyArg ts'
            return $ MkDTTy x ts''
       Nothing -> do m <- getTMap
                     ctx <- getTopLevelCtxt
                     if isHdrCtxt ctx ||     -- Handlers use implicit polym.
                        M.member x m then    -- x can be in val ty contexts
                          return $ MkTVar x
                     else idError x "type variable"
refineVType (MkSCTy ty) = refineCType ty >>= return . MkSCTy
refineVType (MkTVar x) =
  do dtm <- getRDTs
     case M.lookup x dtm of
       Just ps ->
         -- if the data type is parameterised by a single eff var then instantiate it to "£"
         do let ts = case ps of
                       [(_, ET)] -> [EArg (MkAb (MkAbVar "£") M.empty)]
                       _ -> []
            checkArgs x (length ps) (length ts)
            ts' <- mapM refineTyArg ts
            return $ MkDTTy x ts'
       Nothing -> return $ MkTVar x
refineVType MkStringTy = return MkStringTy
refineVType MkIntTy = return MkIntTy
refineVType MkCharTy = return MkCharTy

refineTyArg :: TyArg Raw -> Refine (TyArg Refined)
refineTyArg (VArg t) = VArg <$> refineVType t
refineTyArg (EArg ab) = EArg <$> refineAb ab

refineMH :: [MHCls] -> MHSig -> Refine (TopTm Refined)
refineMH xs (MkSig id ty) = do cs <- mapM refineMHCls ys
                               ty' <- refineCType ty
                               return $ MkDefTm $ MkDef id ty' cs
  where ys = filter (\(MkMHCls id' _) -> id' == id) xs

refineMHCls :: MHCls -> Refine (Clause Refined)
refineMHCls (MkMHCls _ cls) = refineClause cls

-- explicit refinements:
-- + id "x" is refined to 1) MkDataCon:              0-ary constructor if matching
--                        2) MkUse . MkOp . MkCmdId: command operator if matching
--                        3) MkUse . MkOp . MkPoly:  poly multihandler operator if it exists
--                        4) MkUse . MkOp . MkMono:  mono multihandler
-- + applications (MkRawComb) are refined same way as ids
-- + let x = e1 in e2    -->   case e1 {x -> e2}
-- + [x, y, z]           -->   x cons (y cons (z cons nil))
refineUse :: Use Raw -> Refine (Either (Use Refined) (Tm Refined))
refineUse (MkRawId id) =
  do ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     case id `findPair` ctrs of
        Just n -> do checkArgs id n 0
                     return $ Right $ MkDCon $ MkDataCon id []
        Nothing ->
          case id `findPair` cmds of
            Just n -> return $ Left $ MkOp $ MkCmdId id
            -- LC: Do we need to check
            Nothing ->
              case id `findPair` hdrs of
                Just n -> return $ Left $ MkOp $ MkPoly id  -- polytypic (n=0 means: takes no argument, x!)
                -- LC: Same here, check for handler's arity = 0?
                Nothing -> return $ Left $ MkOp $ MkMono id -- monotypic: must be local variable
refineUse (MkRawComb (MkRawId id) xs) =
  do xs' <- mapM refineTm xs
     ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     case id `findPair` ctrs of
        Just n -> do checkArgs id n (length xs')
                     return $ Right $ MkDCon $ MkDataCon id xs'
        Nothing ->
          case id `findPair` cmds of
            Just n -> do checkArgs id n (length xs')
                         return $ Left $ MkApp (MkOp $ MkCmdId id) xs'
            Nothing ->
              case id `findPair` hdrs of
                Just n -> do checkArgs id n (length xs')
                             return $ Left $ MkApp (MkOp $ MkPoly id) xs'
                Nothing -> return $ Left $ MkApp (MkOp $ MkMono id) xs'
refineUse (MkRawComb x xs) =
  do x' <- refineUse x
     case x' of
       Left use -> do xs' <- mapM refineTm xs
                      return $ Left $ MkApp use xs'
       Right _ -> throwError ("expected use but got term: " ++ show x')

refineTm :: Tm Raw -> Refine (Tm Refined)
refineTm (MkLet x t1 t2) =
  do s1 <- refineTm t1
     s2 <- refineTm $ MkSC $ MkSComp [MkCls [MkVPat $ MkVarPat x] t2]
     return $ MkUse $ MkApp (MkOp $ MkPoly "case") [s1, s2]
refineTm (MkSC x) = do x' <- refineSComp x
                       return $ MkSC x'
refineTm (MkStr x) = return $ MkStr x
refineTm (MkInt x) = return $ MkInt x
refineTm (MkChar x) = return $ MkChar x
refineTm (MkList ts) =
  do ts' <- mapM refineTm ts
     return $
       foldr
         (\x y -> MkDCon (MkDataCon "cons" [x, y]))
         (MkDCon (MkDataCon "nil" []))
         ts'
refineTm (MkTmSeq t1 t2) = do t1' <- refineTm t1
                              t2' <- refineTm t2
                              return $ MkTmSeq t1' t2'
refineTm (MkUse u) = do u' <- refineUse u
                        case u' of
                          Left use -> return $ MkUse use
                          Right tm -> return tm

refineSComp :: SComp Raw -> Refine (SComp Refined)
refineSComp (MkSComp xs) = do xs' <- mapM refineClause xs
                              return $ MkSComp xs'

refineClause :: Clause Raw -> Refine (Clause Refined)
refineClause (MkCls ps tm) = do ps' <- mapM refinePattern ps
                                tm' <- refineTm tm
                                return $ MkCls ps' tm'

-- explicit refinements:
-- + command patterns (e.g. <send x -> k>) must refer to existing command and match # of args
refinePattern :: Pattern Raw -> Refine (Pattern Refined)
refinePattern (MkVPat p) = MkVPat <$> refineVPat p
refinePattern (MkCmdPat x ps k) =
  do cmds <- getRCmds
     case x `findPair` cmds of
       Just n -> do checkArgs x n (length ps)
                    ps' <- mapM refineVPat ps
                    return $ MkCmdPat x ps' k
       Nothing -> idError x "command"
refinePattern (MkThkPat x) = return $ MkThkPat x

-- explicit refinements:
-- + variable patterns, e.g. "x", are refined to constructors if "x" is 0-ary constructor
-- + data patterns have to be fully instantiated constructors
-- + cons (%::%) and list patterns ([%, %, %]) become data patterns (cons expressions)
refineVPat :: ValuePat Raw -> Refine (ValuePat Refined)
refineVPat (MkVarPat x) =
  do ctrs <- getRCtrs
     case x `findPair` ctrs of
       Just n -> do checkArgs x n 0
                    return $ MkDataPat x []
       Nothing -> return $ MkVarPat x
refineVPat (MkDataPat x xs) =
  do ctrs <- getRCtrs
     case x `findPair` ctrs of
       Just n -> do checkArgs x n (length xs)
                    xs' <- mapM refineVPat xs
                    return $ MkDataPat x xs'
       Nothing -> idError x "constructor"
refineVPat (MkIntPat i) = return $ MkIntPat i
refineVPat (MkCharPat c) = return $ MkCharPat c
refineVPat (MkStrPat s) = return $ MkStrPat s
refineVPat (MkConsPat x xs) =
  do x' <- refineVPat x
     xs' <- refineVPat xs
     return $ MkDataPat "cons" [x', xs']
refineVPat (MkListPat ps) =
  do ps' <- mapM refineVPat ps
     return $
       foldr
         (\x y -> MkDataPat "cons" [x, y])
         (MkDataPat "nil" [])
         ps'

checkArgs :: Id -> Int -> Int -> Refine ()
checkArgs x exp act =
  if exp /= act then
    throwError $ x ++ " expects " ++ show exp ++
                 " argument(s) but " ++ show act ++
                 " given."
  else return ()

idError :: Id -> String -> Refine a
idError x cls = throwError $ "no " ++ cls ++ " named '" ++ x ++ "' declared"

initialiseRState :: [TopTm Raw] -> Refine ()
initialiseRState xs =
  do i <- getRState
     let itfs = getItfs xs
         dts = getDataTs xs
         hdrSigs = getHdrSigs xs
     xs <- foldM addItf (interfaces i) itfs
     ys <- foldM addDataT (datatypes i) dts
     zs <- foldM addMH (handlers i) hdrSigs
     cmds <- foldM addCmd (cmds i) (concatMap getCmds itfs)
     ctrs <- foldM addCtr (ctrs i) (concatMap getCtrs dts)
     putRItfs xs
     putRDTs ys
     putRCmds cmds
     putRCtrs ctrs
     putRMHs zs

makeIntBinOp :: Char -> MHDef Refined
makeIntBinOp c = MkDef [c] (MkCType [MkPort (MkAdj M.empty) MkIntTy
                                    ,MkPort (MkAdj M.empty) MkIntTy]
                            (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)) []

-- Return true if the data type definition contains a computation type
-- with an implicit effect variable "£".
polyDataT :: DataT Raw -> Bool
polyDataT (MkDT _ _ xs) = any polyCtr xs

-- Return true if the interface definition contains a computation type
-- with an implicit/explicit effect variable "£".
polyItf :: Itf Raw -> Bool
polyItf (MkItf _ _ xs) = any polyCmd xs

polyCmd :: Cmd Raw -> Bool
polyCmd (MkCmd _ _ ts t) = any polyVType ts || polyVType t

polyCtr :: Ctr Raw -> Bool
polyCtr (MkCtr _ ts) = any polyVType ts

polyVType :: VType Raw -> Bool
polyVType (MkDTTy _ ts) = any polyTyArg ts
polyVType (MkSCTy ty)   = polyCType ty
polyVType (MkTVar _)    = False
polyVType MkStringTy    = False
polyVType MkIntTy       = False
polyVType MkCharTy      = False

polyCType :: CType Raw -> Bool
polyCType (MkCType ports peg) = any polyPort ports || polyPeg peg

polyPort :: Port Raw -> Bool
polyPort (MkPort adj ty) = polyAdj adj || polyVType ty

polyAdj :: Adj Raw -> Bool
polyAdj (MkAdj itfmap) = polyItfMap itfmap

polyPeg :: Peg Raw -> Bool
polyPeg (MkPeg ab ty) = polyAb ab || polyVType ty

polyAb :: Ab Raw -> Bool
polyAb (MkAb v m) = polyAbMod v || polyItfMap m

polyItfMap :: ItfMap Raw -> Bool
polyItfMap m = any (any polyTyArg) m

polyAbMod :: AbMod Raw -> Bool
polyAbMod MkEmpAb       = False
polyAbMod (MkAbVar "£") = True
polyAbMod (MkAbVar _)   = False

polyTyArg :: TyArg Raw -> Bool
polyTyArg (VArg t)  = polyVType t
polyTyArg (EArg ab) = polyAb ab

{-- The initial state for the refinement pass. -}

builtinDataTs :: [DataT Refined]
builtinDataTs = [MkDT "List" [("X", VT)] [MkCtr "cons" [MkTVar "X"
                                                       ,MkDTTy "List" [VArg (MkTVar "X")]]
                                      ,MkCtr "nil" []]
                ,MkDT "Unit" [] [MkCtr "unit" []]]


builtinItfs :: [Itf Refined]
builtinItfs = [MkItf "Console" [] [MkCmd "inch" [] [] MkCharTy
                                  ,MkCmd "ouch" [] [MkCharTy]
                                                   (MkDTTy "Unit" [])]]

builtinMHDefs :: [MHDef Refined]
builtinMHDefs = map makeIntBinOp "+-" ++ [caseDef]

caseDef :: MHDef Refined
caseDef = MkDef
          "case"
          (MkCType
            [MkPort (MkAdj M.empty) (MkTVar "X")
            ,MkPort (MkAdj M.empty)
             (MkSCTy (MkCType [MkPort (MkAdj M.empty) (MkTVar "X")]
                      (MkPeg (MkAb (MkAbVar "£") M.empty) (MkTVar "Y"))))]
            (MkPeg (MkAb (MkAbVar "£") M.empty) (MkTVar "Y")))
          [MkCls
            [MkVPat (MkVarPat "x"), MkVPat (MkVarPat "f")]
            (MkUse (MkApp (MkOp $ MkMono "f") [MkUse (MkOp (MkMono "x"))]))]

builtinMHs :: [IPair]
builtinMHs = map add builtinMHDefs
  where add (MkDef x (MkCType ps _) _) = (x,length ps)

builtinDTs :: DTMap
builtinDTs = foldl add M.empty builtinDataTs
  where add m (MkDT id ps _) = M.insert id ps m

builtinIFs :: IFMap
builtinIFs = foldl add M.empty builtinItfs
  where add m (MkItf id ps _) = M.insert id ps m

builtinCtrs :: [IPair]
builtinCtrs = map add $ concatMap getCtrs builtinDataTs
  where add (MkCtr id ts) = (id,length ts)

builtinCmds :: [IPair]
builtinCmds = map add $ concatMap getCmds builtinItfs
  where add (MkCmd id _ ts _) = (id,length ts)

initRefine :: RState
initRefine = MkRState builtinIFs builtinDTs builtinMHs builtinCtrs
             builtinCmds (MkProg []) M.empty S.empty Nothing
