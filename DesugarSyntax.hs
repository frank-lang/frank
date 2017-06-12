{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving,TypeSynonymInstances,FlexibleInstances #-}
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

freshRTVar :: Id -> Desugar (VType Desugared)
freshRTVar x = do n <- fresh
                  return $ MkRTVar $ x ++ "$r" ++ (show n)

freshRigid :: Id -> Desugar Id
freshRigid x = do n <- fresh
                  return $ x ++ "$r" ++ show n

pullId :: VType Desugared -> Id
pullId (MkRTVar id) = id
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
desugarTopTm (MkDataTm dt) = MkDataTm <$> desugarDataT dt
desugarTopTm (MkItfTm itf) = MkItfTm <$> desugarItf itf
desugarTopTm (MkDefTm def) = MkDefTm <$> desugarMHDef def

-- explicit refinements:
-- + type variables get fresh ids
desugarDataT :: DataT Refined -> Desugar (DataT Desugared)
desugarDataT (MkDT dt ps                ctrs) =
--                 id val & eff ty vars constructors
  do -- generate fresh ids for ty vars
     xs' <- mapM (freshRigid . fst) ps
     -- map old value type variables to fresh ones
     putEnv $ M.fromList [(x, MkRTVar x') | ((x, VT), x') <- zip ps xs']
     -- map old effect type variables to fresh ones
     putAbModEnv $ M.fromList [(x, MkAbRVar x') | ((x, ET), x') <- zip ps xs']
     -- [(new var name, val or eff)]
     let ps' = [(x', k) | ((_, k), x') <- zip ps xs']

     -- the following will only use but not modify the DState
     ctrs' <- mapM desugarCtr ctrs
     -- ps' contains new fresh names
     return $ MkDT dt ps' ctrs'

-- explicit refinements:
-- + type variables get fresh ids
desugarItf :: Itf Refined -> Desugar (Itf Desugared)
desugarItf (MkItf itf ps cmds) =
  do -- generate fresh ids for type variables
     xs' <- mapM (freshRigid . fst) ps
     let env' = M.fromList [(x, MkRTVar x') | ((x, VT), x') <- zip ps xs']       -- map old value type variables to fresh ones
     let abModEnv' = M.fromList [(x, MkAbRVar x') | ((x, ET), x') <- zip ps xs'] -- map old effect type variables to fresh ones
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

     return $ MkItf itf ps' cmds'

-- no explicit refinements
desugarMHDef :: MHDef Refined -> Desugar (MHDef Desugared)
desugarMHDef (MkDef hdr ty xs) =
  do ty' <- desugarCType ty
     xs' <- mapM desugarClause xs
     return $ MkDef hdr ty' xs'

-- explicit refinements:
-- + type variables get fresh ids
desugarCmd :: Cmd Refined -> Desugar (Cmd Desugared)
desugarCmd (MkCmd cmd  ps                 xs       y) =
--                id   val & eff ty vars  arg tys  return ty
  do -- generate fresh ids for type variables
     ps' <- mapM (freshRigid . fst) ps
     -- map old value type variables to fresh ones
     putEnv $ M.fromList [(p, MkRTVar p') | ((p, VT), p') <- zip ps ps']
     -- map old effect type variables to fresh ones
     putAbModEnv $ M.fromList [(p, MkAbRVar p') | ((p, ET), p') <- zip ps ps']
     -- [(new var name, val or eff)]
     let ps'' = [(p', k) | ((_, k), p') <- zip ps ps']

     xs' <- mapM desugarVType xs
     y' <- desugarVType y
     return $ MkCmd cmd ps'' xs' y'

-- no explicit refinements
desugarCtr :: Ctr Refined -> Desugar (Ctr Desugared)
desugarCtr (MkCtr ctr xs) = do xs' <- mapM desugarVType xs
                               return $ MkCtr ctr xs'

-- explicit refinements:
-- + replace val ty vars by corresponding MkRTVar's of env,
--   generate new fresh one and add if not in env yet
-- + replace 'String' by 'List Char'
desugarVType :: VType Refined -> Desugar (VType Desugared)
desugarVType (MkTVar x) =
  do env <- getEnv
     case M.lookup x env of
       Nothing -> do ty <- freshRTVar x
                     putEnv $ M.insert x ty env
                     return ty
       Just ty -> return ty
desugarVType (MkDTTy dt ts) = do ts' <- mapM desugarTyArg ts
                                 return $ MkDTTy dt ts'
desugarVType (MkSCTy ty) = MkSCTy <$> desugarCType ty
-- replace 'String' by 'List Char'
desugarVType MkStringTy = return $ desugaredStrTy
desugarVType MkIntTy = return $ MkIntTy
desugarVType MkCharTy = return $ MkCharTy

-- nothing happens on this level
desugarTyArg :: TyArg Refined -> Desugar (TyArg Desugared)
desugarTyArg (VArg t) = VArg <$> desugarVType t
desugarTyArg (EArg ab) = EArg <$> desugarAb ab

-- nothing happens on this level
desugarCType :: CType Refined -> Desugar (CType Desugared)
desugarCType (MkCType ports peg) =
  MkCType <$> mapM desugarPort ports <*> desugarPeg peg

-- nothing happens on this level
desugarPort :: Port Refined -> Desugar (Port Desugared)
desugarPort (MkPort adj ty) = MkPort <$> desugarAdj adj <*> desugarVType ty

-- nothing happens on this level
desugarPeg :: Peg Refined -> Desugar (Peg Desugared)
desugarPeg (MkPeg ab ty) = MkPeg <$> desugarAb ab <*> desugarVType ty

-- nothing happens on this level
desugarAb :: Ab Refined -> Desugar (Ab Desugared)
desugarAb (MkAb v m) = do v' <- desugarAbMod v
                          m' <- mapM (mapM desugarTyArg) m
                          return $ MkAb v' m'

-- explicit desugaring:
-- + replace effect type variables by corresponding MkAbRVar's of abModEnv,
--   generate new fresh one and add if not in env yet
desugarAbMod :: AbMod Refined -> Desugar (AbMod Desugared)
desugarAbMod MkEmpAb = return MkEmpAb
desugarAbMod (MkAbVar x) =
  do env <- getAbModEnv
     case M.lookup x env of
       Nothing -> do n <- fresh
                     let var = MkAbRVar (x ++ "$r" ++ (show n))
                     putAbModEnv $ M.insert x var env
                     return var
       Just var -> return var

-- nothing happens on this level
desugarAdj :: Adj Refined -> Desugar (Adj Desugared)
desugarAdj (MkAdj m) = MkAdj <$> mapM (mapM desugarTyArg) m

-- no explicit desugaring: clauses (and constituents) unaffected between Refine/Desugar phase
desugarClause :: Clause Refined -> Desugar (Clause Desugared)
desugarClause (MkCls ps tm) = do ps' <- mapM desugarPattern ps
                                 tm' <- desugarTm tm
                                 return $ MkCls ps' tm'

desugarTm :: Tm Refined -> Desugar (Tm Desugared)
desugarTm (MkSC x) = MkSC <$> desugarSComp x
desugarTm (MkStr s) = return $ MkStr s
desugarTm (MkInt n) = return $ MkInt n
desugarTm (MkChar c) = return $ MkChar c
desugarTm (MkTmSeq tm1 tm2) = MkTmSeq <$> desugarTm tm1 <*> desugarTm tm2
desugarTm (MkUse u) = MkUse <$> desugarUse u
desugarTm (MkDCon d) = MkDCon <$> desugarDCon d

desugarPattern :: Pattern Refined -> Desugar (Pattern Desugared)
desugarPattern (MkVPat v) = MkVPat <$> desugarVPat v
desugarPattern (MkCmdPat c vs k) = do vs' <- mapM desugarVPat vs
                                      return $ MkCmdPat c vs' k
desugarPattern (MkThkPat x) = return $ MkThkPat x

desugarVPat :: ValuePat Refined -> Desugar (ValuePat Desugared)
desugarVPat (MkVarPat x) = return $ MkVarPat x
desugarVPat (MkDataPat x xs) = MkDataPat x <$> mapM desugarVPat xs
desugarVPat (MkIntPat i) = return $ MkIntPat i
desugarVPat (MkCharPat c) = return $ MkCharPat c
desugarVPat (MkStrPat s) = return $ MkStrPat s


desugarSComp :: SComp Refined -> Desugar (SComp Desugared)
desugarSComp (MkSComp xs) = MkSComp <$> mapM desugarClause xs

desugarUse :: Use Refined -> Desugar (Use Desugared)
desugarUse (MkApp use xs) = MkApp <$> desugarUse use <*> mapM desugarTm xs
desugarUse (MkOp op) = return $ MkOp op

desugarDCon :: DataCon Refined -> Desugar (DataCon Desugared)
desugarDCon (MkDataCon id xs) = MkDataCon id <$> mapM desugarTm xs

-- Test program
testProg :: Prog Refined
testProg = MkProg $
           [MkDataTm $ MkDT "TypeA" [("X", VT), ("Y", VT)]
            [MkCtr "one" [MkTVar "X"]
            ,MkCtr "two" [MkTVar "X"
                         ,MkTVar "Y"]]
           ,MkDataTm $ MkDT "TypeB" [("X", VT)] [MkCtr "Just" [MkTVar "X"]]
           ,MkDefTm $ MkDef "k"
            (MkCType [MkPort (MkAdj M.empty) (MkTVar "X")
                     ,MkPort (MkAdj M.empty) (MkTVar "Y")]
             (MkPeg (MkAb (MkAbVar "£") M.empty) (MkTVar "X"))) []]

