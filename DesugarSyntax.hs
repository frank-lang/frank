{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving,TypeSynonymInstances,FlexibleInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

-- Transform all type variables to unique rigid type variables.
module DesugarSyntax where

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map.Strict as M

import Syntax
import FreshNames

type Desugar = StateT DState (FreshMT Identity)

type IdTVMap = M.Map Id (VType Desugared)

type IdAbModMap = M.Map Id (AbMod Desugared)

data DState = MkDState { env :: IdTVMap
                       , abModEnv :: IdAbModMap }

getDState :: Desugar DState
getDState = get

putDState :: DState -> Desugar ()
putDState = put

freshRTVar :: Id -> Desugared -> Desugar (VType Desugared)
freshRTVar x a = do n <- fresh
                    return $ RTVar (x ++ "$r" ++ (show n)) a

freshRigid :: Id -> Desugar Id
freshRigid x = do n <- fresh
                  return $ x ++ "$r" ++ show n

pullId :: VType Desugared -> Id
pullId (RTVar id _) = id
pullId _ = error "pullId called on something other than a rigid tvar"

putEnv :: IdTVMap -> Desugar ()
putEnv p = do s <- getDState
              putDState $ s { env = p }

getEnv :: Desugar IdTVMap
getEnv = do s <- getDState
            return $ env s

putAbModEnv :: IdAbModMap -> Desugar ()
putAbModEnv p = do s <- getDState
                   putDState $ s { abModEnv = p }

getAbModEnv :: Desugar IdAbModMap
getAbModEnv = do s <- getDState
                 return $ abModEnv s


initDState :: DState
initDState = MkDState M.empty M.empty

desugar :: Prog Refined -> Prog Desugared
desugar (MkProg xs) = MkProg $ evalFresh m
  where m = evalStateT (mapM desugarTopTm' xs) initDState
        desugarTopTm' tm =
          do putEnv $ M.empty -- purge mappings from previous context.
             desugarTopTm tm

-- no explicit refinements
desugarTopTm :: TopTm Refined -> Desugar (TopTm Desugared)
desugarTopTm (DataTm dt a) = DataTm <$> desugarDataT dt <*> pure (refToDesug a)
desugarTopTm (ItfTm itf a) = ItfTm <$> desugarItf itf <*> pure (refToDesug a)
desugarTopTm (DefTm def a) = DefTm <$> desugarMHDef def <*> pure (refToDesug a)

-- explicit refinements:
-- + type variables get fresh ids
desugarDataT :: DataT Refined -> Desugar (DataT Desugared)
desugarDataT (DT dt ps                ctrs a) = do
  -- id val & eff ty vars constructors
  -- generate fresh ids for ty vars
  xs' <- mapM (freshRigid . fst) ps
  -- map old value type variables to fresh ones
  putEnv $ M.fromList [(x, RTVar x' a') | ((x, VT), x') <- zip ps xs']
  -- map old effect type variables to fresh ones
  putAbModEnv $ M.fromList [(x, AbRVar x' a') | ((x, ET), x') <- zip ps xs']
  -- [(new var name, val or eff)]
  let ps' = [(x', k) | ((_, k), x') <- zip ps xs']
   -- the following will only use but not modify the DState
  ctrs' <- mapM desugarCtr ctrs
  -- ps' contains new fresh names
  return $ DT dt ps' ctrs' a'
  where a' = refToDesug a

-- explicit refinements:
-- + type variables get fresh ids
desugarItf :: Itf Refined -> Desugar (Itf Desugared)
desugarItf (Itf itf ps cmds a) = do
  -- generate fresh ids for type variables
  xs' <- mapM (freshRigid . fst) ps
  let env' = M.fromList [(x, RTVar x' a') | ((x, VT), x') <- zip ps xs']       -- map old value type variables to fresh ones
  let abModEnv' = M.fromList [(x, AbRVar x' a') | ((x, ET), x') <- zip ps xs'] -- map old effect type variables to fresh ones
  -- [(new var name, val or eff)]
  let ps' = [(x', k) | ((_, k), x') <- zip ps xs']

  -- before desugaring each cmd, we need to reset the env
  cmds' <- mapM (\c -> do putEnv env'
                          putAbModEnv abModEnv'
                          desugarCmd c)
                cmds
  -- reset afterwards, too
  putEnv env'
  putAbModEnv abModEnv'
  return $ Itf itf ps' cmds' a'
  where a' = refToDesug a

-- no explicit refinements
desugarMHDef :: MHDef Refined -> Desugar (MHDef Desugared)
desugarMHDef (Def hdr ty xs a) = do
  ty' <- desugarCType ty
  xs' <- mapM desugarClause xs
  return $ Def hdr ty' xs' (refToDesug a)

-- explicit refinements:
-- + type variables get fresh ids
desugarCmd :: Cmd Refined -> Desugar (Cmd Desugared)
desugarCmd (Cmd cmd  ps                 xs       y a) = do
  --  id   val & eff ty vars  arg tys  return ty
  -- generate fresh ids for type variables
  ps' <- mapM (freshRigid . fst) ps
  -- map old value type variables to fresh ones
  putEnv $ M.fromList [(p, RTVar p' a') | ((p, VT), p') <- zip ps ps']
  -- map old effect type variables to fresh ones
  putAbModEnv $ M.fromList [(p, AbRVar p' a') | ((p, ET), p') <- zip ps ps']
  -- [(new var name, val or eff)]
  let ps'' = [(p', k) | ((_, k), p') <- zip ps ps']
  xs' <- mapM desugarVType xs
  y' <- desugarVType y
  return $ Cmd cmd ps'' xs' y' a'
  where a' = refToDesug a

-- no explicit refinements
desugarCtr :: Ctr Refined -> Desugar (Ctr Desugared)
desugarCtr (Ctr ctr xs a) = do
  xs' <- mapM desugarVType xs
  return $ Ctr ctr xs' (refToDesug a)

-- explicit refinements:
-- + replace val ty vars by corresponding MkRTVar's of env,
--   generate new fresh one and add if not in env yet
-- + replace 'String' by 'List Char'
desugarVType :: VType Refined -> Desugar (VType Desugared)
desugarVType (TVar x a) =
  do env <- getEnv
     case M.lookup x env of
       Nothing -> do ty <- freshRTVar x (refToDesug a)
                     putEnv $ M.insert x ty env
                     return ty
       Just ty -> return ty
desugarVType (DTTy dt ts a) = do ts' <- mapM desugarTyArg ts
                                 return $ DTTy dt ts' (refToDesug a)
desugarVType (SCTy ty a) = do ty' <- desugarCType ty
                              return $ SCTy ty' (refToDesug a)
-- replace 'String' by 'List Char'
desugarVType (StringTy a) = return $ desugaredStrTy (refToDesug a)
desugarVType (IntTy a) = return $ IntTy (refToDesug a)
desugarVType (CharTy a) = return $ CharTy (refToDesug a)

-- nothing happens on this level
desugarTyArg :: TyArg Refined -> Desugar (TyArg Desugared)
desugarTyArg (VArg t a) = VArg <$> desugarVType t <*> pure (refToDesug a)
desugarTyArg (EArg ab a) = EArg <$> desugarAb ab <*> pure (refToDesug a)

-- nothing happens on this level
desugarCType :: CType Refined -> Desugar (CType Desugared)
desugarCType (CType ports peg a) =
  CType <$> mapM desugarPort ports <*> desugarPeg peg <*> pure (refToDesug a)

-- nothing happens on this level
desugarPort :: Port Refined -> Desugar (Port Desugared)
desugarPort (Port adj ty a) = Port <$> desugarAdj adj <*> desugarVType ty <*> pure (refToDesug a)

-- nothing happens on this level
desugarPeg :: Peg Refined -> Desugar (Peg Desugared)
desugarPeg (Peg ab ty a) = Peg <$> desugarAb ab <*> desugarVType ty <*> pure (refToDesug a)

-- nothing happens on this level
desugarAb :: Ab Refined -> Desugar (Ab Desugared)
desugarAb (Ab v (ItfMap m b) a) = do v' <- desugarAbMod v
                                     m' <- mapM (mapM desugarTyArg) m
                                     return $ Ab v' (ItfMap m' (refToDesug b)) (refToDesug a)

-- explicit desugaring:
-- + replace effect type variables by corresponding MkAbRVar's of abModEnv,
--   generate new fresh one and add if not in env yet
desugarAbMod :: AbMod Refined -> Desugar (AbMod Desugared)
desugarAbMod (EmpAb a) = return $ EmpAb (refToDesug a)
desugarAbMod (AbVar x a) =
  do env <- getAbModEnv
     case M.lookup x env of
       Nothing -> do n <- fresh
                     let var = AbRVar (x ++ "$r" ++ (show n)) (refToDesug a)
                     putAbModEnv $ M.insert x var env
                     return var
       Just var -> return var

-- nothing happens on this level
desugarAdj :: Adj Refined -> Desugar (Adj Desugared)
desugarAdj (Adj (ItfMap m b) a) = do m' <- mapM (mapM desugarTyArg) m
                                     return $ Adj (ItfMap m' (refToDesug b)) (refToDesug a)

-- no explicit desugaring: clauses (and constituents) unaffected between Refine/Desugar phase
desugarClause :: Clause Refined -> Desugar (Clause Desugared)
desugarClause (Cls ps tm a) = do ps' <- mapM desugarPattern ps
                                 tm' <- desugarTm tm
                                 return $ Cls ps' tm' (refToDesug a)

desugarTm :: Tm Refined -> Desugar (Tm Desugared)
desugarTm (SC x a) = SC <$> desugarSComp x <*> pure (refToDesug a)
desugarTm (StrTm s a) = return $ StrTm s (refToDesug a)
desugarTm (IntTm n a) = return $ IntTm n (refToDesug a)
desugarTm (CharTm c a) = return $ CharTm c (refToDesug a)
desugarTm (TmSeq tm1 tm2 a) = TmSeq <$> desugarTm tm1 <*> desugarTm tm2 <*> pure (refToDesug a)
desugarTm (Use u a) = Use <$> desugarUse u <*> pure (refToDesug a)
desugarTm (DCon d a) = DCon <$> desugarDCon d <*> pure (refToDesug a)

desugarPattern :: Pattern Refined -> Desugar (Pattern Desugared)
desugarPattern (VPat v a) = VPat <$> desugarVPat v <*> pure (refToDesug a)
desugarPattern (CmdPat c vs k a) = do vs' <- mapM desugarVPat vs
                                      return $ CmdPat c vs' k (refToDesug a)
desugarPattern (ThkPat x a) = return $ ThkPat x (refToDesug a)

desugarVPat :: ValuePat Refined -> Desugar (ValuePat Desugared)
desugarVPat (VarPat x a) = return $ VarPat x (refToDesug a)
desugarVPat (DataPat x xs a) = DataPat x <$> mapM desugarVPat xs <*> pure (refToDesug a)
desugarVPat (IntPat i a) = return $ IntPat i (refToDesug a)
desugarVPat (CharPat c a) = return $ CharPat c (refToDesug a)
desugarVPat (StrPat s a) = return $ StrPat s (refToDesug a)


desugarSComp :: SComp Refined -> Desugar (SComp Desugared)
desugarSComp (SComp xs a) = SComp <$> mapM desugarClause xs <*> pure (refToDesug a)

desugarUse :: Use Refined -> Desugar (Use Desugared)
desugarUse (App use xs a) = App <$> desugarUse use <*> mapM desugarTm xs <*> pure (refToDesug a)
desugarUse (Op op a) = Op <$> desugarOperator op <*> pure (refToDesug a)

desugarOperator :: Operator Refined -> Desugar (Operator Desugared)
desugarOperator (Mono x a) = return $ Mono x (refToDesug a)
desugarOperator (Poly x a) = return $ Poly x (refToDesug a)
desugarOperator (CmdId x a) = return $ CmdId x (refToDesug a)

desugarDCon :: DataCon Refined -> Desugar (DataCon Desugared)
desugarDCon (DataCon id xs a) = DataCon id <$> mapM desugarTm xs <*> pure (refToDesug a)

-- Helpers

refToDesug :: Refined -> Desugared
refToDesug (Refined loc) = Desugared loc
