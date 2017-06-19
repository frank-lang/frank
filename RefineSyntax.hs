{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax
import RefineSyntaxCommon
import RefineSyntaxConcretiseEps
import RefineSyntaxSubstitItfAliases

import Debug.Trace

-- Main refinement function
refine :: Prog Raw -> Either String (Prog Refined)
refine prog = evalState (runExceptT (refine' prog)) initRefine

-- Explicit refinements:
-- + check if main function exists
-- + built-in data types, interfaces, operators are added
refine' :: Prog Raw -> Refine (Prog Refined)
refine' (MkProg xs) = do
  initialiseRState xs
  let (sigs, defs, dts, itfs, itfAls) = splitTopTm xs
  -- Refine top level terms
  putTopLevelCtxt Datatype
  dtTms <- mapM refineDataT dts
  putTopLevelCtxt Interface
  itfTms <- mapM refineItf itfs
  putTopLevelCtxt InterfaceAlias
  itfAlTms <- mapM refineItfAl itfAls
  putTopLevelCtxt Handler
  hdrs <- mapM (refineMH defs) sigs
  if existsMain hdrs then
    return $ MkProg (map MkDataTm builtinDataTs ++ dtTms ++
                     map MkItfTm builtinItfs ++ itfTms ++
                     map MkDefTm builtinMHDefs ++ hdrs)
  else throwError $ "no main function defined."

existsMain :: [TopTm Refined] -> Bool
existsMain ((MkDefTm (MkDef id _ _)) : xs) = id == "main" || existsMain xs
existsMain [] = False
existsMain (_ : xs) = error "invalid top term: expected multihandler"

-- Explicit refinements:
-- + data type has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineDataT :: DataT Raw -> Refine (TopTm Refined)
refineDataT (MkDT dt ps           ctrs) =
 --         data dt p_1 ... p_m = ctr_1 | ... | ctr_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine constructors
       putTMap (M.fromList $ zip tvs (map MkTVar tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       ctrs' <- mapM refineCtr ctrs
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ MkDataTm $ MkDT dt ps ctrs'
  else throwError $ "duplicate parameter in datatype " ++ dt

-- Explicit refinements:
-- + interface has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineItf :: Itf Raw -> Refine (TopTm Refined)
refineItf (MkItf itf ps      cmds) =
--        interface itf p_1 ... p_m = cmd_1 | ... | cmd_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine commands
       putTMap (M.fromList $ zip tvs (map MkTVar tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       cmds' <- mapM refineCmd cmds
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ MkItfTm $ MkItf itf ps cmds'
  else throwError $ "duplicate parameter in interface " ++ itf

-- Explicit refinements:
-- + interface has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineItfAl :: ItfAlias Raw -> Refine (ItfAlias Refined)
refineItfAl (MkItfAlias itfAl ps _) =
--          interface itf p_1 ... p_m = [itf_1 t_11 ... t_1n, ...]
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine itf map
       putTMap (M.fromList $ zip tvs (map MkTVar tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       -- interpret RHS of interface alias def. as the instantiation of itf with
       -- the generic type variables ps (this "lift" is possible as the
       -- itf map of itf is part of the RState)
       let singletonItfMap = M.singleton itfAl (map tyVar2rawTyVarArg ps)
       itfMap' <- refineItfMap $ singletonItfMap
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ MkItfAlias itfAl ps itfMap'
  else throwError $ "duplicate parameter in interface alias " ++ itfAl

-- Explicit refinements:
-- + command has unique effect & type variables
-- + implicit eff var [£] is defined explicitly
refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd (MkCmd id ps xs y) =
--        id : forall p_1 ... p_m, x_1 -> ... -> x_n -> y
  if uniqueIds (map fst ps) then
    do tmap <- getTMap
       evset <- getEVSet
       -- check that none of this cmd's ty vars coincide with the itf's ones
       if uniqueIds (map fst ps ++ map fst (M.toList tmap) ++ S.toList evset) then
         do
           let tvs = [x | (x, VT) <- ps] -- val ty vars
           let evs = [x | (x, ET) <- ps] -- eff ty vars
           -- refine argument types and result type
           -- first, add temp. val, eff ty vars
           putTMap (M.union tmap (M.fromList $ zip tvs (map MkTVar tvs)))
           putEVSet (S.union evset (S.fromList evs))
           -- then, refine
           xs' <- mapM refineVType xs
           y' <- refineVType y
           -- finally, reset temp. val, eff ty vars
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
refineAb (MkAb v m) =
--       [v | itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln]
  do -- Check if itf_i contains effect variable
     es <- getEVars $ M.toList m
     if null es then do m' <- refineItfMap m
                        return $ MkAb (refineAbMod v) m'
     else if length es == 1 then do let u = head es
                                    m' <- refineItfMap (M.delete u m)
                                    return $ MkAb (MkAbVar u) m'
     else throwError $ "ability has multiple effect variables " ++ (show es)

-- Input: itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln
-- If a itf_i is an already-introduced effect variable, require that there are
--   no x_ij (else throw error)
-- Output: all itf_i which refer to already-introduced effect variables
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

-- Explicit refinements:
-- + implicit [£] ty args to interfaces are made explicit
refineItfMap :: ItfMap Raw -> Refine (ItfMap Refined)
refineItfMap m = do
  -- replace interface aliases by interfaces
  xs <- concat <$> mapM substitItfAls (M.toList m)
  -- refine each interface
  xs' <- mapM refineEntry xs
  return $ M.fromList xs'
  where refineEntry :: (Id, [TyArg Raw]) -> Refine (Id, [TyArg Refined])
        refineEntry (x, ts) =
--                  x t_1 ... t_n
          do itfs <- getRItfs
             case M.lookup x itfs of
               Just ps ->
--               1) interface x p_1 ... p_n     = ...
--            or 2) interface x p_1 ... p_n [£] = ...
--                  and [£] has been explicitly added before
--                            if 2), set t_{n+1} := [£]
                 do let ts' = if length ps == length ts + 1 &&
                                 (snd (ps !! length ts) == ET) then
                                   ts ++ [EArg (MkAb (MkAbVar "£") M.empty)]
                              else ts
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

-- Explicit refinements:
-- + implicit [£] ty args to data types are made explicit
-- + MkDTTy is distinguished between being (in the following precedence)
--   1) data type indeed            -> MkDTTy
--   2) (implicitly) intro'd ty var -> MkTVar  (if no ty args)
--   3) neither                     -> error
-- + MkTVar is distinguished between being
--   1) intro'd ty var              -> MkTVar
--   2) data type                   -> MkDTTy
--   3) neither                     -> MkTVar
-- + ty arguments refer only to introduced val tys
refineVType :: VType Raw -> Refine (VType Refined)
refineVType (MkDTTy x  ts) =
--           x t_1 ... t_n
  do dtm <- getRDTs
     case M.lookup x dtm of
       Just ps -> do
--        1) data x p_1 ... p_n
--    or  2) data x p_1 ... p_n [£]       ([£] has been explicitly added before)
                      -- If 2), set t_{n+1} := [£]
         let ts' = if length ps == length ts + 1 &&
                      (snd (ps !! length ts) == ET) then
                     ts ++ [EArg (MkAb (MkAbVar "£") M.empty)]
                   else ts
         checkArgs x (length ps) (length ts')
         ts'' <- mapM refineTyArg ts'
         return $ MkDTTy x ts''
       Nothing -> do
         m <- getTMap
         ctx <- getTopLevelCtxt
         if null ts &&  -- there must be no arguments to ty var
            (isHdrCtxt ctx || -- x can be implic. poly. ty var in hdr sign.
             M.member x m)    -- x can be in val ty contexts
         then return $ MkTVar x
         else idError x "type variable"
refineVType (MkSCTy ty) = refineCType ty >>= return . MkSCTy
refineVType (MkTVar x) =
  do tmap <- getTMap
     dtm <- getRDTs
     case M.lookup x tmap of
       Just _  -> return $ MkTVar x
       Nothing -> case M.lookup x dtm of
         Just ps ->
           -- if the data type is parameterised by a single eff var then instantiate it to [£|]
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

-- Explicit refinements:
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
            -- LC: Do we need to check command's arity = 0?
            Nothing ->
              case id `findPair` hdrs of
                -- polytypic (n=0 means: takes no argument, x!)
                Just n -> return $ Left $ MkOp $ MkPoly id
                -- LC: Same here, check for handler's arity = 0?
                -- monotypic: must be local variable
                Nothing -> return $ Left $ MkOp $ MkMono id
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

-- Explicit refinements:
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

-- Explicit refinements:
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

idError :: Id -> String -> Refine a
idError x cls = throwError $ "no " ++ cls ++ " named '" ++ x ++ "' declared"

initialiseRState :: [TopTm Raw] -> Refine ()
initialiseRState xs =
  do i <- getRState
     let (dts', itfs', itfAls') = concretiseEps (getDataTs xs) (getItfs xs) (getItfAliases xs)
         hdrs'   = getHdrSigs xs
     itfs   <- foldM addItf      (interfaces i)       itfs'
     itfAls <- foldM addItfAlias (interfaceAliases i) itfAls'
     dts    <- foldM addDataT    (datatypes i)        dts'
     hdrs   <- foldM addMH       (handlers i)         hdrs'
     cmds   <- foldM addCmd      (cmds i)             (concatMap getCmds itfs')
     ctrs   <- foldM addCtr      (ctrs i)             (concatMap getCtrs dts')
     putRItfs       itfs
     putRItfAliases itfAls
     putRDTs        dts
     putRCmds       cmds
     putRCtrs       ctrs
     putRMHs        hdrs

makeIntBinOp :: Char -> MHDef Refined
makeIntBinOp c = MkDef [c] (MkCType [MkPort (MkAdj M.empty) MkIntTy
                                    ,MkPort (MkAdj M.empty) MkIntTy]
                            (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)) []

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

builtinItfAliases :: [ItfAlias Raw]
builtinItfAliases = []

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

builtinIFAliases :: IFAliasesMap
builtinIFAliases = foldl add M.empty builtinItfAliases
  where add m (MkItfAlias id ps itfMap) = M.insert id (ps, itfMap) m

builtinCtrs :: [IPair]
builtinCtrs = map add $ concatMap getCtrs builtinDataTs
  where add (MkCtr id ts) = (id,length ts)

builtinCmds :: [IPair]
builtinCmds = map add $ concatMap getCmds builtinItfs
  where add (MkCmd id _ ts _) = (id,length ts)

initRefine :: RState
initRefine = MkRState builtinIFs builtinIFAliases builtinDTs builtinMHs builtinCtrs
             builtinCmds (MkProg []) M.empty S.empty Nothing

{- Helper functions -}

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

splitTopTm :: [TopTm Raw] -> ([MHSig], [MHCls], [DataT Raw], [Itf Raw], [ItfAlias Raw])
splitTopTm xs = (getHdrSigs xs, getHdrDefs xs [], dts, itfs, itfAliases)
  where dts = getDataTs xs
        itfs = getItfs xs
        itfAliases = getItfAliases xs

-- Add the name if not already present
addEntry :: [IPair] -> Id -> Int -> String -> Refine [IPair]
addEntry xs x n prefix = if x `mem` xs then throwError (prefix ++ x ++
                                                        " already defined.")
                         else return $ (x,n) : xs

-- addItf :: [IPair] -> Itf a -> Refine [IPair]
-- addItf xs (MkItf x ps _) = addEntry xs x (length ps) "duplicate interface: "

addItf :: IFMap -> Itf a -> Refine IFMap
addItf m (MkItf x ps _) = if M.member x m then
                             throwError ("duplicate interface: " ++ x ++
                                         " already defined.")
                           else return $ M.insert x ps m

addItfAlias :: IFAliasesMap -> ItfAlias Raw -> Refine (IFAliasesMap)
addItfAlias m (MkItfAlias x ps itfMap) = if M.member x m then
                                            throwError ("duplicate interface alias: " ++ x ++
                                                        " already defined.")
                                         else return $ M.insert x (ps, itfMap) m

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
