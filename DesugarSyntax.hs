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

desugarTopTm :: TopTm Refined -> Desugar (TopTm Desugared)
desugarTopTm (MkDataTm dt) = MkDataTm <$> desugarDataT dt
desugarTopTm (MkItfTm itf) = MkItfTm <$> desugarItf itf
desugarTopTm (MkDefTm def) = MkDefTm <$> desugarMHDef def

desugarDataT :: DataT Refined -> Desugar (DataT Desugared)
desugarDataT (MkDT dt ps ctrs) =
  do xs' <- mapM (freshRigid . fst) ps
     putEnv $ M.fromList [(x, MkRTVar x') | ((x, VT), x') <- zip ps xs']
     putAbModEnv $ M.fromList [(x, MkAbRVar x') | ((x, ET), x') <- zip ps xs']
     let ps' = [(x', k) | ((_, k), x') <- zip ps xs']

     -- we know that the following will not modify the environments so
     -- we do not need to backup and restore them
     ctrs' <- mapM desugarCtr ctrs
     return $ MkDT dt ps' ctrs'

desugarItf :: Itf Refined -> Desugar (Itf Desugared)
desugarItf (MkItf itf ps cmds) =
  do xs' <- mapM (freshRigid . fst) ps
     putEnv $ M.fromList [(x, MkRTVar x') | ((x, VT), x') <- zip ps xs']
     putAbModEnv $ M.fromList [(x, MkAbRVar x') | ((x, ET), x') <- zip ps xs']
     let ps' = [(x', k) | ((_, k), x') <- zip ps xs']

     cmds' <- mapM desugarCmd cmds
     return $ MkItf itf ps' cmds'

desugarMHDef :: MHDef Refined -> Desugar (MHDef Desugared)
desugarMHDef (MkDef hdr ty xs) =
  do ty' <- desugarCType ty
     xs' <- mapM desugarClause xs
     return $ MkDef hdr ty' xs'

desugarCmd :: Cmd Refined -> Desugar (Cmd Desugared)
desugarCmd (MkCmd cmd xs y) = do xs' <- mapM desugarVType xs
                                 y' <- desugarVType y
                                 return $ MkCmd cmd xs' y'

desugarCtr :: Ctr Refined -> Desugar (Ctr Desugared)
desugarCtr (MkCtr ctr xs) = do xs' <- mapM desugarVType xs
                               return $ MkCtr ctr xs'

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
desugarVType MkStringTy = return $ desugaredStrTy
desugarVType MkIntTy = return $ MkIntTy
desugarVType MkCharTy = return $ MkCharTy

desugarTyArg :: TyArg Refined -> Desugar (TyArg Desugared)
desugarTyArg (VArg t) = VArg <$> desugarVType t
desugarTyArg (EArg ab) = EArg <$> desugarAb ab

desugarCType :: CType Refined -> Desugar (CType Desugared)
desugarCType (MkCType ports peg) =
  MkCType <$> mapM desugarPort ports <*> desugarPeg peg

desugarPort :: Port Refined -> Desugar (Port Desugared)
desugarPort (MkPort adj ty) = MkPort <$> desugarAdj adj <*> desugarVType ty

desugarPeg :: Peg Refined -> Desugar (Peg Desugared)
desugarPeg (MkPeg ab ty) = MkPeg <$> desugarAb ab <*> desugarVType ty

desugarAb :: Ab Refined -> Desugar (Ab Desugared)
desugarAb (MkAb v m) = do v' <- desugarAbMod v
                          m' <- mapM (mapM desugarTyArg) m
                          return $ MkAb v' m'

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


desugarAdj :: Adj Refined -> Desugar (Adj Desugared)
desugarAdj (MkAdj m) = MkAdj <$> mapM (mapM desugarTyArg) m

-- Clauses (and constituents) unaffected between Refined/Desugared phase
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

