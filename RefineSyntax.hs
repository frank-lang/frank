module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Functor.Identity

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import BwdFwd
import Syntax
import RefineSyntaxCommon
import RefineSyntaxConcretiseEps
import RefineSyntaxSubstitItfAliases
import Debug

-- Main refinement function
refine :: Prog Raw -> Either String (Prog Refined)
refine prog = evalState (runExceptT (refine' prog)) initRefine

-- Explicit refinements:
-- + concretise epsilons in top level definitions
-- + built-in data types, interfaces, operators are added
refine' :: Prog Raw -> Refine (Prog Refined)
refine' (MkProg xs) = do
  -- Concretise epsilon vars
  let (dts, itfs, itfAls) = concretiseEps [d | DataTm d _ <- xs]
                                          [i | ItfTm i _ <- xs]
                                          [i | ItfAliasTm i _ <- xs]
  let hdrSigs = [s | SigTm s _ <- xs]
  let hdrDefs = [c | ClsTm c _ <- xs]
  let rawBuiltinItfTms = map (\itf -> ItfTm itf b) builtinItfs
  let builtinMHDTms = map (\hdr -> DefTm hdr a) builtinMHDefs
  -- Initialise refinement state
  initialiseRState dts itfs itfAls
  -- Refine top level terms
  putTopLevelCtxt Datatype
  dtTms <- mapM refineDataT dts
  putTopLevelCtxt Interface
  itfTms <- mapM refineItf itfs
  putTopLevelCtxt InterfaceAlias
  mapM_ refineItfAl itfAls
  putTopLevelCtxt Handler
  hdrs <- mapM (refineMH hdrDefs) hdrSigs
  -- Make sure (built-in) interfaces and interface aliases have unique ids
  -- Performing this check after refinement to prioritise more precise error
  -- messages.
  checkUniqueIds ([i | i@(ItfTm _ _) <- xs] ++
                  [i | i@(ItfAliasTm _ _) <- xs] ++
                  [i | i@(ItfTm _ _) <- rawBuiltinItfTms])
    (errorRefDuplTopTm "interface/interface alias")
  -- Check uniqueness of hdrs w.r.t builtin ones
  checkUniqueIds ([h | h@(DefTm _ _) <- hdrs] ++
                  [h | h@(DefTm _ _) <- builtinMHDTms])
    (errorRefDuplTopTm "operator")
  builtinItfTms <- mapM refineItf builtinItfs
  return $ MkProg (map (\dt -> DataTm dt a) builtinDataTs ++ dtTms ++
                   builtinItfTms ++ itfTms ++ builtinMHDTms ++ hdrs)
  where a = Refined BuiltIn
        b = Raw BuiltIn

-- Explicit refinements:
-- + data type has unique effect & type variables
refineDataT :: DataT Raw -> Refine (TopTm Refined)
refineDataT d@(DT dt ps ctrs a) =
 --         data dt p_1 ... p_m = ctr_1 | ... | ctr_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine constructors
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       ctrs' <- mapM refineCtr ctrs
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ DataTm (DT dt ps ctrs' a') a'
  else throwError $ errorRefDuplParamData d
  where a' = rawToRef a

-- Explicit refinements:
-- + interface has unique effect & type variables
refineItf :: Itf Raw -> Refine (TopTm Refined)
refineItf i@(Itf itf ps cmds a) =
--        interface itf p_1 ... p_m = cmd_1 | ... | cmd_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine commands
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       cmds' <- mapM refineCmd cmds
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ ItfTm (Itf itf ps cmds' a') a'
  else throwError $ errorRefDuplParamItf i
  where a' = rawToRef a

-- Explicit refinements:
-- + interface has unique effect & type variables
refineItfAl :: ItfAlias Raw -> Refine ()
refineItfAl i@(ItfAlias itfAl ps _ a) =
--          interface itf p_1 ... p_m = [itf_1 t_11 ... t_1n, ...]
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine itf map
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       -- interpret RHS of interface alias def. as the instantiation of itf with
       -- the generic type variables ps (this "lift" is possible as the
       -- itf map of itf is part of the RState)
       let singletonItfMap = ItfMap (M.singleton itfAl (BEmp :< map tyVar2rawTyVarArg ps)) (Raw Generated)
       itfMap' <- refineItfMap singletonItfMap
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
  else throwError $ errorRefDuplParamItfAl i
  where a' = rawToRef a

-- Explicit refinements:
-- + command has unique effect & type variables
refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd c@(Cmd id ps xs y a) =
--        id p_1 ... p_m: x_1 -> ... -> x_n -> y
  if uniqueIds (map fst ps) then
    do tmap <- getTMap
       evset <- getEVSet
       -- TODO: LC: Shadowing should be allowed, fix this in future
       -- check that none of this cmd's ty vars coincide with the itf's ones
       if uniqueIds (map fst ps ++ map fst (M.toList tmap) ++ S.toList evset) then
         do let tvs = [x | (x, VT) <- ps] -- val ty vars
            let evs = [x | (x, ET) <- ps] -- eff ty vars
            -- refine ty args
            putTMap (M.union tmap (M.fromList $ zip tvs (map (swap TVar a) tvs))) -- temp. val ty vars
            putEVSet (S.union evset (S.fromList evs))    -- temp. eff ty vars
            xs' <- mapM refineVType xs
            y' <- refineVType y
            putTMap tmap                                 -- reset
            putEVSet evset                               -- reset
            return $ Cmd id ps xs' y' a'
       else throwError $ "a type parameter of command " ++ id ++
                         "already occurs as interface type parameter"
  else throwError $ errorRefDuplParamCmd c
  where a' = rawToRef a


refineCtr :: Ctr Raw -> Refine (Ctr Refined)
refineCtr (Ctr id xs a) = do xs' <- mapM refineVType xs
                             return $ Ctr id xs' (rawToRef a)

refineCType :: CType Raw -> Refine (CType Refined)
refineCType (CType xs z a) = do ys <- mapM refinePort xs
                                peg <- refinePeg z
                                return $ CType ys peg (rawToRef a)

refinePort :: Port Raw -> Refine (Port Refined)
refinePort (Port adjs ty a) = do adjs' <- mapM refineAdj adjs
                                 ty' <- refineVType ty
                                 return $ Port (concat adjs') ty' (rawToRef a)

refinePeg :: Peg Raw -> Refine (Peg Refined)
refinePeg (Peg ab ty a) = do ab' <- refineAb ab
                             ty' <- refineVType ty
                             return $ Peg ab' ty' (rawToRef a)

refineAb :: Ab Raw -> Refine (Ab Refined)
refineAb (Ab v mp@(ItfMap m _) a) =
--       [v | itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln]
  do -- Check that v has been introduced before or is now implicitly introduced
     evset <- getEVSet
     ctx <- getTopLevelCtxt
     case v of
       (EmpAb b) -> do m' <- refineItfMap mp
                       return $ Ab (EmpAb (rawToRef b)) m' a'
       (AbVar x b) ->
         if x `S.member` evset || isHdrCtxt ctx then
            do m' <- refineItfMap mp
               return $ Ab (AbVar x (rawToRef b)) m' a'
         else throwError $ errorRefIdNotDeclared "effect type variable" x a
  where a' = rawToRef a

-- Input: itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln
-- If a itf_i is an already-introduced effect variable, require that there are
--   no x_ij (else throw error)
-- Output: all itf_i which refer to already-introduced effect variables
getIntroducedEVars :: ItfMap Raw -> Refine [Id]
getIntroducedEVars (ItfMap m _) = do
  p <- getEVSet
  let candidates = [(itf, (maximum . map length . bwd2fwd) xs) | (itf, xs) <- M.toList m, S.member itf p]
  let errors = filter (\(itf, n) -> n > 0) candidates
  case errors of []             -> return $ map fst candidates
                 ((itf, _) : _) -> throwError $ errorRefEffVarNoParams itf

refineAbMod :: AbMod Raw -> AbMod Refined
refineAbMod (EmpAb a) = EmpAb (rawToRef a)
refineAbMod (AbVar x a) = AbVar x (rawToRef a)

refineAdj :: Adjustment Raw -> Refine [Adjustment Refined]
refineAdj (ConsAdj x ts a) = do
  tss' <- refineItfInst a (x, ts)
  let tss'' = M.foldlWithKey (\acc itf ts' -> acc ++ instsToAdjs itf ts') [] tss'
  --LAST STOP
  return $ tss''
  where instsToAdjs :: Id -> Bwd [TyArg Refined] -> [Adjustment Refined]
        instsToAdjs itf ts = map (\ts' -> ConsAdj itf ts' (rawToRef a)) (bwd2fwd ts)
refineAdj (AdaptorAdj adp a) = do
  adp' <- refineAdaptor adp
  return $ [AdaptorAdj adp' (rawToRef a)]

-- Explicit refinements:
-- + interface aliases are substituted
refineItfInst :: Raw -> (Id, [TyArg Raw]) ->
                 Refine (M.Map Id (Bwd [TyArg Refined]))
refineItfInst a (x, ts) = do
--                  x t_11 ... t_1n
  -- replace interface aliases by interfaces
  m' <- substitItfAls (x, ts) >>= \i -> case i of
    ItfMap m _ -> pure m
    _ -> throwError "Expected ItfMap but found something else."
--                  x t_11 ... t_1n, ..., x t_m1 t_mn
  -- refine instantiations of each interface
  m'' <- M.fromList <$> (mapM (refineItfInsts a)) (M.toList m')
  return m''

-- Explicit refinements:
-- + interface aliases are substituted
refineItfMap :: ItfMap Raw -> Refine (ItfMap Refined)
refineItfMap (ItfMap m a) = do
  -- replace interface aliases by interfaces
  ms <- mapM (\(x, insts) -> mapM (\inst -> substitItfAls (x, inst)) (bwd2fwd insts)) (M.toList m)
  let (ItfMap m' a') = foldl plusItfMap (emptyItfMap a) (concat ms)
  -- refine instantiations of each interface
  m'' <- M.fromList <$> (mapM (refineItfInsts a)) (M.toList m')
  return $ ItfMap m'' (rawToRef a)

refineItfInsts :: Raw -> (Id, Bwd [TyArg Raw]) ->
                  Refine (Id, Bwd [TyArg Refined])
refineItfInsts a (x, insts) = do
--                  x t_11 ... t_1n, ..., x t_m1 t_mn
  itfs <- getRItfs
  case M.lookup x itfs of
    Just ps -> do
--            1) interface x p_1 ... p_n     = ...
--         or 2) interface x p_1 ... p_n [£] = ...
--               and [£] has been explicitly added before
--            if 2), set t_{n+1} := [£]
       evset <- getEVSet
       ctx <- getTopLevelCtxt
       insts' <- mapM (\ts -> do let a' = Raw (implicitNear a)
                                 let ts' = if "£" `S.member` evset ||
                                              isHdrCtxt ctx
                                           then concretiseEpsArg ps ts a'
                                           else ts
                                 checkArgs x (length ps) (length ts') a
                                 mapM refineTyArg ts')
                      insts
       return (x, insts')
    Nothing -> throwError $ errorRefIdNotDeclared "interface" x a

-- Explicit refinements:
-- + implicit [£] ty args to data types are made explicit
-- + DTTy is distinguished between being (in the following precedence)
--   1) data type indeed            -> DTTy
--   2) (implicitly) intro'd ty var -> TVar  (if no ty args)
--   3) neither                     -> error
-- + MkTVar is distinguished between being
--   1) intro'd ty var              -> TVar
--   2) data type                   -> DTTy
--   3) neither                     -> TVar
-- + ty arguments refer only to introduced val tys
refineVType :: VType Raw -> Refine (VType Refined)
refineVType (DTTy x ts a) =
--           x t_1 ... t_n
  do -- Check that x is datatype or introduced or just-implicitly intro'd ty var
     dtm <- getRDTs
     tmap <- getTMap
     ctx <- getTopLevelCtxt
     evset <- getEVSet
     case M.lookup x dtm of
       Just ps -> do
--       data x p_1 ... p_n
         let a' = Raw (implicitNear a)
         let ts' = if "£" `S.member` evset || isHdrCtxt ctx
                   then concretiseEpsArg ps ts a'
                   else ts
         checkArgs x (length ps) (length ts') a
         ts'' <- mapM refineTyArg ts'
         return $ DTTy x ts'' (rawToRef a)
       Nothing ->
         if null ts &&          -- there must be no arguments to ty var
            (isHdrCtxt ctx ||   -- x can be implic. ty var in hdr sign.
             x `M.member` tmap)    -- x can be in val ty contexts
         then return $ TVar x (rawToRef a)
         else throwError $ errorRefIdNotDeclared "value type variable" x a
refineVType (SCTy ty a) = refineCType ty >>= return . swap SCTy (rawToRef a)
refineVType (TVar x a) =
  do -- Check that x is intro'd ty-var or datatype or just-implicitly intro'd ty var
     tmap <- getTMap
     dtm <- getRDTs
     ctx <- getTopLevelCtxt
     case M.lookup x tmap of
       Just _  -> return $ TVar x (rawToRef a)
       Nothing -> case M.lookup x dtm of
         Just ps ->
           -- if the data type is parameterised by a single eff var then instantiate it to [£|]
           do let ts = case ps of
                         [(_, ET)] -> [EArg (Ab (AbVar "£" a) (ItfMap M.empty a) a) a]
                         _ -> []
              checkArgs x (length ps) (length ts) a
              ts' <- mapM refineTyArg ts
              return $ DTTy x ts' (rawToRef a)
         Nothing ->
           -- last possibility: x can be implic. ty var in hdr sign.
           if isHdrCtxt ctx
           then return $ TVar x (rawToRef a)
           else throwError $ errorRefIdNotDeclared "value type variable" x a
refineVType (StringTy a) = return $ StringTy (rawToRef a)
refineVType (IntTy a) = return $ IntTy (rawToRef a)
refineVType (CharTy a) = return $ CharTy (rawToRef a)
refineVType (FloatTy a) = return $ FloatTy (rawToRef a)

refineTyArg :: TyArg Raw -> Refine (TyArg Refined)
refineTyArg (VArg t a) = VArg <$> refineVType t <*> pure (rawToRef a)
refineTyArg (EArg ab a) = EArg <$> refineAb ab <*> pure (rawToRef a)

refineMH :: [MHCls Raw] -> MHSig Raw -> Refine (TopTm Refined)
refineMH xs (Sig id ty a) = do cs <- mapM refineMHCls ys
                               ty' <- refineCType ty
                               return $ DefTm (Def id ty' cs a') a'
  where ys = filter (\(MHCls id' _ _) -> id' == id) xs
        a' = rawToRef a

refineMHCls :: MHCls Raw -> Refine (Clause Refined)
refineMHCls (MHCls _ cls a) = refineClause cls

-- Explicit refinements:
-- + id "x" is refined to 1) DataCon:          0-ary constructor if matching
--                        2) Use . Op . CmdId: command operator if matching
--                        3) Use . Op . VarId: value variable otherwise
-- + applications (MkRawComb) are refined same way as ids
-- + let x = e1 in e2    -->   case e1 {x -> e2}
-- + [x, y, z]           -->   x cons (y cons (z cons nil))
refineUse :: Use Raw -> Refine (Either (Use Refined) (Tm Refined))
refineUse (RawId id a) =
  do ctrs <- getRCtrs
     cmds <- getRCmds
     if id `elem` ctrs
       then return $ Right $ DCon (DataCon id [] a') a'
       else if id `elem` cmds
            then return $ Left $ Op (CmdId id a') a'
            else return $ Left $ Op (VarId id a') a'
  where a' = rawToRef a
refineUse (RawComb (RawId id b) xs a) =
  do xs' <- mapM refineTm xs
     ctrs <- getRCtrs
     cmds <- getRCmds
     if id `elem` ctrs
       then return $ Right $ DCon (DataCon id xs' b') a'
       else if id `elem` cmds
            then return $ Left $ App (Op (CmdId id b') b') xs' a'
            else return $ Left $ App (Op (VarId id b') b') xs' a'
  where a' = rawToRef a
        b' = rawToRef b
refineUse (RawComb x xs a) =
  do x' <- refineUse x
     case x' of
       Left use -> do xs' <- mapM refineTm xs
                      return $ Left $ App use xs' (rawToRef a)
       Right tm -> throwError $ errorRefExpectedUse tm
refineUse (Adapted rs t a) =
  -- First check the existence of the interfaces
  do rs' <- mapM refineAdaptor rs
     t' <- refineUse t
     case t' of
       Left u   -> return $ Left $ Adapted rs' u (rawToRef a)
       Right tm -> throwError $ errorRefExpectedUse tm

refineAdaptor :: Adaptor Raw -> Refine (Adaptor Refined)
refineAdaptor adp@(RawAdp x liat left right a) = do
  itfCx <- getRItfs
  if x `M.member` itfCx then
    -- TODO: LC: left-hand side must consist of distinct names
    -- Check whether first element of right-hand side is liat
    if null right || head right == liat then
      if null right then return $ Adp x Nothing [] (rawToRef a)
      else
        let mm = Just (length left) in
        let right' = tail right in
        let rightNs = map (\p -> elemIndex p (reverse left)) right' in
        if any isNothing rightNs then throwError "adaptor error"
        else return $ Adp x (Just (length left)) (map fromJust rightNs) (rawToRef a)
    else
      throwError $ "adaptor error"
  else throwError $ errorRefIdNotDeclared "interface" x a

refineTm :: Tm Raw -> Refine (Tm Refined)
refineTm (Let x t1 t2 a) =
  do s1 <- refineTm t1
     s2 <- refineTm $ SC (SComp [Cls [VPat (VarPat x a) a] t2 a] a) a
     return $ Use (App (Op (VarId "case" a') a') [s1, s2] a') a'
  where a' = rawToRef a
refineTm (SC x a) = do x' <- refineSComp x
                       return $ SC x' (rawToRef a)
refineTm (StrTm x a) = return $ StrTm x (rawToRef a)
refineTm (IntTm x a) = return $ IntTm x (rawToRef a)
refineTm (CharTm x a) = return $ CharTm x (rawToRef a)
refineTm (FloatTm x a) = return $ FloatTm x (rawToRef a)
refineTm (ListTm ts a) =
  do ts' <- mapM refineTm ts
     return $
       foldr
         (\x y -> DCon (DataCon "cons" [x, y] a') a')
         (DCon (DataCon "nil" [] a') a')
         ts'
  where a' = rawToRef a
refineTm (TmSeq t1 t2 a) = do t1' <- refineTm t1
                              t2' <- refineTm t2
                              return $ TmSeq t1' t2' (rawToRef a)
refineTm (Use u a) = do u' <- refineUse u
                        case u' of
                          Left use -> return $ Use use (rawToRef a)
                          Right tm -> return tm

refineSComp :: SComp Raw -> Refine (SComp Refined)
refineSComp (SComp xs a) = do xs' <- mapM refineClause xs
                              return $ SComp xs' (rawToRef a)

refineClause :: Clause Raw -> Refine (Clause Refined)
refineClause (Cls ps tm a) = do ps' <- mapM refinePattern ps
                                tm' <- refineTm tm
                                return $ Cls ps' tm' (rawToRef a)

-- Explicit refinements:
-- + command patterns (e.g. <send x -> k>) must refer to existing command.
refinePattern :: Pattern Raw -> Refine (Pattern Refined)
refinePattern (VPat p a) = VPat <$> refineVPat p <*> (pure $ rawToRef a)
refinePattern (CmdPat x n ps k a) =
  do cmds <- getRCmds
     if x `elem` cmds
       then do ps' <- mapM refineVPat ps
               return $ CmdPat x n ps' k (rawToRef a)
       else throwError $ errorRefIdNotDeclared "command" x a
refinePattern (ThkPat x a) = return $ ThkPat x (rawToRef a)

-- Explicit refinements:
-- + variable patterns, e.g. "x", are refined to ctrs if "x" is 0-ary ctr
-- + data patterns have to be defined constructors
-- + cons (%::%) and list patterns ([%, %, %]) become data patterns (cons exps)
refineVPat :: ValuePat Raw -> Refine (ValuePat Refined)
refineVPat (VarPat x a) =
  do ctrs <- getRCtrs
     if x `elem` ctrs
       then return $ DataPat x [] (rawToRef a)
       else return $ VarPat x (rawToRef a)
refineVPat (DataPat x xs a) =
  do ctrs <- getRCtrs
     if x `elem` ctrs
       then do xs' <- mapM refineVPat xs
               return $ DataPat x xs' (rawToRef a)
       else throwError $ errorRefIdNotDeclared "constructor" x a
refineVPat (IntPat i a) = return $ IntPat i (rawToRef a)
refineVPat (CharPat c a) = return $ CharPat c (rawToRef a)
refineVPat (StrPat s a) = return $ StrPat s (rawToRef a)
refineVPat (FloatPat f a) = return $ FloatPat f (rawToRef a)
refineVPat (ConsPat x xs a) =
  do x' <- refineVPat x
     xs' <- refineVPat xs
     return $ DataPat "cons" [x', xs'] (rawToRef a)
refineVPat (ListPat ps a) =
  do ps' <- mapM refineVPat ps
     return $
       foldr
         (\x y -> DataPat "cons" [x, y] (rawToRef a))
         (DataPat "nil" [] (rawToRef a))
         ps'

initialiseRState :: [DataT Raw] -> [Itf Raw] -> [ItfAlias Raw] -> Refine ()
initialiseRState dts itfs itfAls =
  do i <- getRState
     itfs'   <- foldM addItf      (interfaces i)       itfs
     itfAls' <- foldM addItfAlias (interfaceAliases i) itfAls
     dts'    <- foldM addDataT    (datatypes i)        dts
     cmds'   <- foldM addCmd      (cmds i)             (concatMap getCmds itfs)
     ctrs'   <- foldM addCtr      (ctrs i)             (concatMap getCtrs dts)
     putRItfs       itfs'
     putRItfAliases itfAls'
     putRDTs        dts'
     putRCmds       cmds'
     putRCtrs       ctrs'

makeIntBinOp :: Refined -> Char -> MHDef Refined
makeIntBinOp a c = Def [c] (CType [Port [] (IntTy a) a
                                  ,Port [] (IntTy a) a]
                                  (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a) (IntTy a) a) a) [] a

makeIntBinCmp :: Refined -> Char -> MHDef Refined
makeIntBinCmp a c = Def [c] (CType [Port [] (IntTy a) a
                                   ,Port [] (IntTy a) a]
                             (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                              (DTTy "Bool" [] a) a) a) [] a

-- as above, but we now use Flaot instead.
makeFloatBinOp :: Refined -> Char -> MHDef Refined
makeFloatBinOp a c = Def ([c] ++ "~") (CType [Port [] (FloatTy a) a
                                         ,Port [] (FloatTy a) a]
                                         (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a) (FloatTy a) a) a) [] a

makeFloatBinCmp :: Refined -> Char -> MHDef Refined
makeFloatBinCmp a c = Def ([c] ++ "~") (CType [Port [] (FloatTy a) a
                                          ,Port [] (FloatTy a) a]
                                          (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                                               (DTTy "Bool" [] a) a) a) [] a

{-- The initial state for the refinement pass. -}

builtinDataTs :: [DataT Refined]
builtinDataTs = [DT "List" [("X", VT)] [Ctr "cons" [TVar "X" b
                                                       ,DTTy "List" [VArg (TVar "X" b) b] b] b
                                         ,Ctr "nil" [] b] b
                ,DT "Unit" [] [Ctr "unit" [] b] b
                ,DT "Bool" [] [Ctr "true" [] b, Ctr "false" [] b] b
                ,DT "Ref" [("X", VT)] [] b]
  where b = Refined BuiltIn

builtinItfs :: [Itf Raw]
builtinItfs = [Itf "Console" [] [Cmd "inch" [] [] (CharTy b) b
                                ,Cmd "ouch" [] [CharTy b]
                                 (DTTy "Unit" [] b) b
                                ,Cmd "ouint" [] [IntTy b]
                                 (DTTy "Unit" [] b) b] b
              ,Itf "RefState" [] [Cmd "new" [("X", VT)] [TVar "X" b]
                                                            (DTTy "Ref" [VArg (TVar "X" b) b] b) b
                                   ,Cmd "write" [("X", VT)] [DTTy "Ref" [VArg (TVar "X" b) b] b
                                                             ,TVar "X" b]
                                                             (DTTy "Unit" [] b) b
                                   ,Cmd "read" [("X", VT)] [DTTy "Ref" [VArg (TVar "X" b) b] b]
                                                              (TVar "X" b) b] b]
  where b = Raw BuiltIn

builtinItfAliases :: [ItfAlias Raw]
builtinItfAliases = []

builtinMHDefs :: [MHDef Refined]
builtinMHDefs = map (makeIntBinOp (Refined BuiltIn)) "+-" ++
                map (makeIntBinCmp (Refined BuiltIn)) "><" ++
                map (makeFloatBinOp (Refined BuiltIn)) "+-" ++
                map (makeFloatBinCmp (Refined BuiltIn)) "><" ++
                [caseDef, charEq, alphaNumPred]

charEq :: MHDef Refined
charEq = Def "eqc" (CType [Port [] (CharTy a) a
                          ,Port [] (CharTy a) a]
                          (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                               (DTTy "Bool" [] a) a) a) [] a
  where a = Refined BuiltIn

alphaNumPred :: MHDef Refined
alphaNumPred = Def "isAlphaNum"
               (CType [Port [] (CharTy a) a]
                          (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                               (DTTy "Bool" [] a) a) a) [] a
  where a = Refined BuiltIn

caseDef :: MHDef Refined
caseDef = Def
          "case"
          (CType
            [Port [] (TVar "X" b) b
            ,Port []
             (SCTy (CType [Port [] (TVar "X" b) b]
                      (Peg (Ab (AbVar "£" b) (ItfMap M.empty b) b) (TVar "Y" b) b) b) b) b]
            (Peg (Ab (AbVar "£" b) (ItfMap M.empty b) b) (TVar "Y" b) b) b)
          [Cls
            [VPat (VarPat "x" b) b, VPat (VarPat "f" b) b]
            (Use (App (Op (VarId "f" b) b)
                  [Use (Op (VarId "x" b) b) b] b) b) b] b
  where b = Refined BuiltIn

builtinDTs :: DTMap
builtinDTs = foldl add M.empty builtinDataTs
  where add m (DT id ps _ a) = M.insert id ps m

builtinIFs :: IFMap
builtinIFs = foldl add M.empty builtinItfs
  where add m (Itf id ps _ a) = M.insert id ps m

builtinIFAliases :: IFAliasesMap
builtinIFAliases = foldl add M.empty builtinItfAliases
  where add m (ItfAlias id ps itfMap a) = M.insert id (ps, itfMap) m

builtinCtrs :: [Id]
builtinCtrs = map add $ concatMap getCtrs builtinDataTs
  where add (Ctr id ts a) = id

builtinCmds :: [Id]
builtinCmds = map add $ concatMap getCmds builtinItfs
  where add (Cmd id _ ts _ a) = id

initRefine :: RState
initRefine = MkRState builtinIFs builtinIFAliases builtinDTs builtinCtrs
             builtinCmds M.empty S.empty Nothing

{- Helper functions -}

-- Add the id if not already present
addEntry :: [Id] -> Id -> String -> Refine [Id]
addEntry xs x prefix =
  if x `elem` xs then throwError (errorRefEntryAlreadyDefined prefix x)
  else return $ x : xs

addItf :: IFMap -> Itf Raw -> Refine IFMap
addItf m (Itf x ps _ a) =
  if M.member x m then
    throwError $ errorRefDuplTopTm "interface" x (getSource a)
  else return $ M.insert x ps m

addItfAlias :: IFAliasesMap -> ItfAlias Raw -> Refine IFAliasesMap
addItfAlias m (ItfAlias x ps itfMap a) =
  if M.member x m then
     throwError $ errorRefDuplTopTm "interface alias" x (getSource a)
  else return $ M.insert x (ps, itfMap) m

addDataT :: DTMap -> DataT Raw -> Refine DTMap
addDataT m (DT x ps _ a) =
  if M.member x m then
    throwError $ errorRefDuplTopTm "datatype" x (getSource a)
  else return $ M.insert x ps m

addCtr :: [Id] -> Ctr a -> Refine [Id]
addCtr xs (Ctr x _ _) = addEntry xs x "duplicate constructor:"

addCmd :: [Id] -> Cmd a -> Refine [Id]
addCmd xs (Cmd x _ _ _ _) = addEntry xs x "duplicate command:"

uniqueIds :: [Id] -> Bool
uniqueIds xs = length xs == length (nub xs)

-- Helpers

swap :: (a -> b -> c) -> b -> a -> c
swap f b a = f a b

rawToRef :: Raw -> Refined
rawToRef (Raw loc) = Refined loc
