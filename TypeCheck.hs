-- Inspired by Adam Gundry et al.'s treatment of type inference in
-- context. See Gundry's thesis (most closely aligned) or the paper ``Type
-- inference in Context'' for more details.
{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
module TypeCheck where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import Data.List.Unique

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import Debug.Trace

import BwdFwd
import Syntax
import FreshNames
import TypeCheckCommon
import Unification

type EVMap a = M.Map Id (Ab a)

-- Given an operator, reconstruct its corresponding type assigned via context
-- 1) x is command of interface itf:
--    - Retrieve how itf is instantiated in amb
--    - Add mark and add all type variables qs to context (-> qs')
--    - Unify itf instantiation ps with qs'
--    - Construct susp. comp. val. type whose containted tys are all in current locality
-- 2) x is monotypic (i.e., local variable) or
--         polytypic (i.e., multi-handler)
--    - It must have been assigned a type in the context, return it
find :: Operator -> Contextual (VType Desugared)
find (MkCmdId x) =
  do amb <- getAmbient
     (itf, qs, rs, ts, y) <- getCmd x
     -- interface itf q_1 ... q_m = x: forall r1 ... r_l, t_1 -> ... -> t_n -> y
     mps <- lkpItf itf amb -- how is itf instantiated in amb?
     case mps of
       Nothing -> throwError $ "command " ++ x ++
                  " belonging to interface " ++ itf ++
                  " not permitted by ambient ability:" ++
                  (show $ ppAb amb)
       Just ps ->
         -- instantiation in ambient: [itf p_1 ... p_m]
         do addMark
            qs' <- mapM makeFlexibleTyArg qs
            rs' <- mapM makeFlexibleTyArg rs
            ts' <- mapM makeFlexible ts
            y' <- makeFlexible y
            mapM (uncurry unifyTyArg) (zip ps qs')
            return $ MkSCTy $
              MkCType (map (\x -> MkPort idAdj x) ts') (MkPeg amb y')
find x = getContext >>= find'
  where find' BEmp = throwError $ "'" ++ getOpName x ++ "' not in scope"
        find' (es :< TermVar y ty) | x == y = return ty
        find' (es :< _) = find' es

-- Find the first flexible type definition (as opposed to a hole) in ctx for x
findFTVar :: Id -> Contextual (Maybe (VType Desugared))
findFTVar x = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (TyDefn ty)) | x == y = return $ Just ty
        find' (es :< _) = find' es

-- Run a contextual computation with an additonal term variable in scope
-- 1) Push [x:=ty] on context
-- 2) Run computation m
-- 3) Remove [x:=ty] from context
inScope :: Operator -> VType Desugared -> Contextual a -> Contextual a
inScope x ty m = do modify (:< TermVar x ty)
                    a <- m
                    modify dropVar
                    return a
  where dropVar :: Context -> Context
        dropVar BEmp = error "Invariant violation"
        dropVar (es :< TermVar y _) | x == y = es
        dropVar (es :< e) = dropVar es :< e

-- Run a contextual computation in a modified ambient environment
inAmbient :: Adj Desugared -> Contextual a -> Contextual a
inAmbient adj m = do amb <- getAmbient
                     putAmbient (plus amb adj)
                     a <- m
                     putAmbient amb
                     return a

-- Lookup the ty args of an interface "itf" in a given ability (i.e., how is
-- the interface instantiated?)
-- Return "Nothing" if "itf" is not part of given ability
lkpItf :: Id -> Ab Desugared -> Contextual (Maybe [TyArg Desugared])
lkpItf itf (MkAb v m) =
  case M.lookup itf m of
    Nothing -> lkpItfInAbMod itf v
    Just xs -> return $ Just xs

lkpItfInAbMod :: Id -> AbMod Desugared -> Contextual (Maybe [TyArg Desugared])
lkpItfInAbMod itf (MkAbFVar x) = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (AbDefn ab)) | x == y = lkpItf itf ab
        find' (es :< _) = find' es
lkpItfInAbMod itf v = return Nothing

-- The only operators that could potentially be polymorphic are
-- 1) polytypic operators and
-- 2) command operators
-- We only instantiate here in case 1) because command operators get already
-- instantiated in "find"
-- LC: TODO: remove this function and transfer its functionality to "find", too?
instantiate :: Operator -> VType Desugared -> Contextual (VType Desugared)
instantiate (MkPoly _) ty = addMark >> makeFlexible ty
instantiate _ ty = return ty

-- TODO: change output of check to Maybe String?

-- infer the type of a use w.r.t. the given program
inferEvalUse :: Prog Desugared -> Use Desugared ->
                Either String (VType Desugared)
inferEvalUse p use = runExcept $ evalFreshMT $ evalStateT comp initTCState
  where comp = unCtx $ do _ <- initContextual p
                          inferUse use

-- Main typechecking function
-- - Init TCState
-- - Check each top term
-- - If no exception is thrown during checkTopTm, return input program
check :: Prog Desugared -> Either String (Prog Desugared)
check p = runExcept $ evalFreshMT $ evalStateT (checkProg p) initTCState
--        "unpack" the monad
  where
    checkProg p = unCtx $ do MkProg xs <- initContextual p
                             mapM checkTopTm xs
                             return $ MkProg xs

checkTopTm :: TopTm Desugared -> Contextual ()
checkTopTm (MkDefTm def) = checkMHDef def
checkTopTm _ = return ()

checkMHDef :: MHDef Desugared -> Contextual ()
checkMHDef (MkDef id ty@(MkCType ps q) cs) =
  do mapM_ (\cls -> checkCls cls ps q) cs

-- 1st major TC function: Infer type of a "use"
-- Functions below implement the typing rules described in the paper.
-- 1) Var, PolyVar, Command rules
--    - Find operator x in context and retrieve its type
--    - Case distinction on x:
--      1.1) x is monotypic (local var)
--           - Its type is exactly determined (instantiate does nothing)
--      1.2) x is polytypic (multi-handler) or a command
--           - Its type (susp. comp. ty) possibly contains rigid ty vars
--           - Instantiate all of them (add to context), then return type
-- 2) App rule
--    - Infer type of f
--    - If this susp. comp. type is known, check the arguments are well-typed
--    - If not, create fresh type pattern and unify (constraining for future)
inferUse :: Use Desugared -> Contextual (VType Desugared)
inferUse (MkOp x) = find x >>= (instantiate x)
inferUse (MkApp f xs) =
  do ty <- inferUse (MkOp f)
     discriminate ty
  where -- Check typings of x_i for port p_i
        checkArgs :: [Port Desugared] -> [Tm Desugared] -> Contextual ()
        checkArgs ps xs = mapM_ (uncurry checkArg) (zip ps xs)

        -- Check typing tm: ty in ambient [adj]
        checkArg :: Port Desugared -> Tm Desugared -> Contextual ()
        checkArg (MkPort adj ty) tm = inAmbient adj (checkTm tm ty)

        -- Case distinction on operator's type ty
        -- 1) ty is susp. comp. type
        --    - Check that required abilities of f are admitted (unify with amb)
        --    - Check typings of arguments x_i: p_i in [amb + adj_i] for all i
        -- 2) ty is flex. type var. y
        --    - f must have occured in context as one of these:
        --      2.1) [..., y:=?,   ..., f:=y, ...]
        --           y is not determined yet, create type of right shape
        --           (according to arguments) and constrain ty (unify)
        --      2.2) [..., y:=ty', ..., f:=y, ...]
        --           try 2) again, this time with ty'
        discriminate :: VType Desugared -> Contextual (VType Desugared)
        discriminate ty@(MkSCTy (MkCType ps (MkPeg ab ty'))) =
        -- {p_1 -> ... p_n -> [ab] ty'}
          do amb <- getAmbient
             unifyAb amb ab   -- require [amb] = [ab]
             checkArgs ps xs
             return ty'
        discriminate ty@(MkFTVar y) =
          do mty <- findFTVar y  -- find definition of y in context
             case mty of
               Nothing -> -- 2.1)
                 -- TODO: check that this is correct
                 do addMark
                    amb <- getAmbient
                    ps <- mapM (\_ -> freshPort "X") xs
                    q@(MkPeg ab ty')  <- freshPegWithAb amb "Y"
                    unify ty (MkSCTy (MkCType ps q))
                    return ty'
                 -- errTy ty
               Just ty' -> discriminate ty' -- 2.2)
        discriminate ty = errTy ty

        -- TODO: tidy.
        -- We don't need to report an error here, but rather generate
        -- appropriate fresh type variables as above.
        errTy ty = throwError $
                   "application (" ++ show (MkApp f xs) ++
                   "): expected suspended computation but got " ++
                   (show $ ppVType ty)

-- 2nd major TC function: Check that term (construction) has given type
checkTm :: Tm Desugared -> VType Desugared -> Contextual ()
checkTm (MkSC sc) ty = checkSComp sc ty          -- Thunk rule
checkTm (MkStr _) ty = unify desugaredStrTy ty
checkTm (MkInt _) ty = unify MkIntTy ty
checkTm (MkChar _) ty = unify MkCharTy ty
checkTm (MkTmSeq tm1 tm2) ty =
  -- create dummy mvar s.t. any type of tm1 can be unified with it
  do ftvar <- freshMVar "seq"
     checkTm tm1 (MkFTVar ftvar)
     checkTm tm2 ty
checkTm (MkUse u) t = do s <- inferUse u         -- Switch rule
                         unify t s
checkTm (MkDCon (MkDataCon k xs)) ty =           -- Data rule
  do (dt, args, ts) <- getCtr k
--    data dt arg_1 ... arg_m = k t_1 ... t_n | ...
     addMark
     -- prepare flexible ty vars and ty args
     args' <- mapM makeFlexibleTyArg args
     ts' <- mapM makeFlexible ts
     unify ty (MkDTTy dt args')
     mapM_ (uncurry checkTm) (zip xs ts')

-- Check that susp. comp. term has given type, corresponds to Thunk rule
-- Case distinction on expected type:
-- 1) Check {cls_1 | ... | cls_m} : {p_1 -> ... -> p_n -> q}
-- 2) Check {cls_1 | ... | cls_m} : ty
--    - For each cls_i:
--      - Check against a type of the right shape (of fresh flex. var.s which
--        then get bound via checking
--      - Unify the obtained type for cls_i with overall type ty
checkSComp :: SComp Desugared -> VType Desugared -> Contextual ()
checkSComp (MkSComp xs) (MkSCTy (MkCType ps q)) =
  mapM_ (\cls -> checkCls cls ps q) xs
checkSComp (MkSComp xs) ty = mapM_ (checkCls' ty) xs
  where checkCls' :: VType Desugared -> Clause Desugared -> Contextual ()
        checkCls' ty cls@(MkCls pats tm) =
          do pushMarkCtx
             ps <- mapM (\_ -> freshPort "X") pats
             q <- freshPeg "" "X"
             -- {p_1 -> ... -> p_n -> q} for fresh flex. var.s ps, q
             checkCls cls ps q                -- assign these variables
             unify ty (MkSCTy (MkCType ps q)) -- unify with resulting ty
             purgeMarks

-- create port <i>X for fresh X
freshPort :: Id -> Contextual (Port Desugared)
freshPort x = do ty <- MkFTVar <$> freshMVar x
                 return $ MkPort (MkAdj M.empty) ty

-- create peg [E]Y for fresh E, Y
freshPeg :: Id -> Id -> Contextual (Peg Desugared)
freshPeg x y = do v <- MkAbFVar <$> freshMVar x
                  ty <- MkFTVar <$> freshMVar y
                  return $ MkPeg (MkAb v M.empty) ty

-- create peg [ab]X for given [ab], fresh X
freshPegWithAb :: Ab Desugared -> Id -> Contextual (Peg Desugared)
freshPegWithAb ab x = do ty <- MkFTVar <$> freshMVar x
                         return $ MkPeg ab ty

-- Check that given clause has given susp. comp. type (ports, peg)
checkCls :: Clause Desugared -> [Port Desugared] -> Peg Desugared ->
            Contextual ()
checkCls (MkCls pats tm) ports (MkPeg ab ty)
-- type:     port_1 -> ... -> port_n -> [ab]ty
-- clause:   pat_1     ...    pat_n  =  tm
  | length pats == length ports =
    do pushMarkCtx
       putAmbient ab  -- restrict ambient ability
       bs <- fmap concat $ mapM (uncurry checkPat) (zip pats ports)
       -- Bring any bindings in to scope for checking the term then purge the
       -- marks (and suffixes) in the context created for this clause.
       case null bs of
         True -> do -- Just purge marks
                    checkTm tm ty
                    purgeMarks
         False -> do -- Push all bindings to context, then check tm, then remove bindings,
                     -- finally purge marks.
                     foldl1 (.) (map (uncurry inScope) bs) $ checkTm tm ty
                     purgeMarks
  | otherwise = throwError "number of patterns not equal to number of ports"

-- Check that given pattern matches given port
checkPat :: Pattern Desugared -> Port Desugared -> Contextual [TermBinding]
checkPat (MkVPat vp) (MkPort _ ty) = checkVPat vp ty
checkPat (MkCmdPat cmd xs g) (MkPort adj ty) =
-- interface itf q_1 ... q_m =
--   cmd : forall r_1 ... r_l, t_1 -> ... -> t_n -> y | ...

-- port:     <itf p_1 ... p_m> ty
-- pattern:  <cmd x_1 ... x_n -> g>
  do (itf, qs, rs, ts, y) <- getCmd cmd
     mps <- lkpItf itf (plus (MkAb MkEmpAb M.empty) adj) -- how is itf instantiated in adj?
     case mps of
       Nothing -> throwError $
                  "command " ++ cmd ++ " not found in adjustment " ++
                  (show $ ppAdj adj)
       Just ps -> do addMark -- localise the following type variables
                     qs' <- mapM makeFlexibleTyArg qs
                     rs' <- mapM makeFlexibleTyArg rs
                     ts' <- mapM makeFlexible ts
                     y' <- makeFlexible y
                     -- instantiate interface (according to adjustment)
                     mapM (uncurry unifyTyArg) (zip ps qs')
                     -- check command patterns against spec. in interface def.
                     bs <- fmap concat $ mapM (uncurry checkVPat) (zip xs ts')
                     kty <- contType y' adj ty -- type of continuation:  {y' -> [adj + currentAmb]ty}
                     -- bindings: continuation + patterns
                     return ((MkMono g,kty) : bs)
checkPat (MkThkPat x) (MkPort adj ty) =
-- pattern:  x
  do amb <- getAmbient
     return $ [(MkMono x, MkSCTy $ MkCType [] (MkPeg (plus amb adj) ty))]

-- continuation type
contType :: VType Desugared -> Adj Desugared -> VType Desugared ->
            Contextual (VType Desugared)
contType x adj y =
  do amb <- getAmbient
     return $ MkSCTy $ MkCType [MkPort idAdj x] (MkPeg (plus amb adj) y)

-- Check that a value pattern has a given type (corresponding to rules)
-- Return its bindings (id -> value type)
checkVPat :: ValuePat Desugared -> VType Desugared -> Contextual [TermBinding]
checkVPat (MkVarPat x) ty = return [(MkMono x, ty)]  -- P-Var rule
--         x
checkVPat (MkDataPat k ps) ty =                      -- P-Data rule
--         k p_1 .. p_n
  do (dt, args, ts) <- getCtr k
--   data dt arg_1 .. arg_m = k t_1 .. t_n | ...
     addMark
     args' <- mapM makeFlexibleTyArg args
     ts' <- mapM makeFlexible ts
     unify ty (MkDTTy dt args')
     bs <- fmap concat $ mapM (uncurry checkVPat) (zip ps ts')
     return bs
checkVPat (MkCharPat _) ty = unify ty MkCharTy >> return []
checkVPat (MkStrPat _) ty = unify ty desugaredStrTy >> return []
checkVPat (MkIntPat _) ty = unify ty MkIntTy >> return []
-- checkVPat p ty = throwError $ "failed to match value pattern " ++
--                  (show p) ++ " with type " ++ (show ty)

-- Given a type as input, any contained rigid (val/eff) ty var is made flexible
-- The context is thereby extended.
-- Case distinction over contained rigid (val/eff) ty var:
-- 1) it is already part of current locality (up to the Mark)
--    -> return its occuring name
-- 2) it is not part of current locality
--    -> create fresh name in context and return
makeFlexible :: VType Desugared -> Contextual (VType Desugared)
makeFlexible (MkDTTy id ts) = MkDTTy id <$> mapM makeFlexibleTyArg ts
makeFlexible (MkSCTy cty) = MkSCTy <$> makeFlexibleCType cty
makeFlexible (MkRTVar x) = MkFTVar <$> (getContext >>= find')
-- find' either creates a new FlexMVar in current locality or identifies the one already existing
  where find' BEmp = freshMVar x
        find' (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' (es :< Mark) = freshMVar x  -- only search in current locality
        find' (es :< _) = find' es

makeFlexible ty = return ty

makeFlexibleAb :: Ab Desugared -> Contextual (Ab Desugared)
makeFlexibleAb (MkAb v m) = case v of
  MkAbRVar x -> do v' <- MkAbFVar <$> (getContext >>= (find' x))
                   m' <- mapM (mapM makeFlexibleTyArg) m
                   return $ MkAb v' m'
  _ ->          do m' <- mapM (mapM makeFlexibleTyArg) m
                   return $ MkAb v m'
-- find' either creates a new FlexMVar in current locality or identifies the one already existing
  where find' x BEmp = freshMVar x
        find' x (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' x (es :< Mark) = freshMVar x
        find' x (es :< _) = find' x es

makeFlexibleTyArg :: TyArg Desugared -> Contextual (TyArg Desugared)
makeFlexibleTyArg (VArg t)  = VArg <$> makeFlexible t
makeFlexibleTyArg (EArg ab) = EArg <$> makeFlexibleAb ab

makeFlexibleAdj :: Adj Desugared -> Contextual (Adj Desugared)
makeFlexibleAdj (MkAdj m) = MkAdj <$> mapM (mapM makeFlexibleTyArg) m

makeFlexibleCType :: CType Desugared -> Contextual (CType Desugared)
makeFlexibleCType (MkCType ps q) = MkCType <$>
                                   mapM makeFlexiblePort ps <*>
                                   makeFlexiblePeg q

makeFlexiblePeg :: Peg Desugared -> Contextual (Peg Desugared)
makeFlexiblePeg (MkPeg ab ty) = MkPeg <$>
                                makeFlexibleAb ab <*>
                                makeFlexible ty

makeFlexiblePort :: Port Desugared -> Contextual (Port Desugared)
makeFlexiblePort (MkPort adj ty) = MkPort <$>
                                   makeFlexibleAdj adj <*>
                                   makeFlexible ty
