-- Inspired by Adam Gundry et al.'s treatment of type inference in
-- context. See Gundry's thesis (most closely aligned) or the paper ``Type
-- inference in Context'' for more details.
{-# LANGUAGE FlexibleInstances,StandaloneDeriving,TypeSynonymInstances,
             MultiParamTypeClasses,GeneralizedNewtypeDeriving,
             FlexibleContexts,GADTs #-}
{-# LANGUAGE ViewPatterns #-}
module TypeCheck where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import Data.List.Unique

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import BwdFwd
import Syntax
import FreshNames
import TypeCheckCommon
import Unification
import Debug

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
find :: Operator Desugared -> Contextual (VType Desugared)
find (CmdId x a) =
  do amb <- getAmbient
     (itf, qs, rs, ts, y) <- getCmd x
     -- interface itf q_1 ... q_m = x: forall r1 ... r_l, t_1 -> ... -> t_n -> y
     mps <- lkpItf itf amb -- how is itf instantiated in amb?
     logBeginFindCmd x itf mps
     case mps of
       Nothing -> throwError $ errorFindCmdNotPermit x a itf amb
       Just ps ->
         -- instantiation in ambient: [itf p_1 ... p_m]
         do addMark
            -- Localise qs, bind them to their instantiation
            -- (according to adjustment) and localise their occurences
            -- in ts, y
            qs' <- mapM (makeFlexibleTyArg []) qs
            ts' <- mapM (makeFlexible []) ts
            y' <- makeFlexible [] y
            mapM (uncurry unifyTyArg) (zip ps qs')
            -- Localise rs
            rs' <- mapM (makeFlexibleTyArg []) rs
            let ty = SCTy (CType (map (\x -> Port idAdjDesug x a) ts') (Peg amb y' a) a) a
            logEndFindCmd x ty
            return ty
find x = getContext >>= find'
  where find' BEmp = throwError $ errorTCNotInScope x
        find' (es :< TermVar y ty) | strip x == strip y = return ty
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
inScope :: Operator Desugared -> VType Desugared -> Contextual a -> Contextual a
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
lkpItf itf (Ab v (ItfMap m _) _) =
  case M.lookup itf m of
    Nothing -> lkpItfInAbMod itf v
    Just xs -> return $ Just xs

lkpItfInAbMod :: Id -> AbMod Desugared -> Contextual (Maybe [TyArg Desugared])
lkpItfInAbMod itf (AbFVar x _) = getContext >>= find'
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
instantiate :: Operator Desugared -> VType Desugared -> Contextual (VType Desugared)
instantiate (Poly _ _) ty = addMark >> makeFlexible [] ty
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
                             theCtx <- getContext
                             mapM checkTopTm xs
                             return $ MkProg xs

checkTopTm :: TopTm Desugared -> Contextual ()
checkTopTm (DefTm def _) = checkMHDef def
checkTopTm _ = return ()

checkMHDef :: MHDef Desugared -> Contextual ()
checkMHDef (Def id ty@(CType ps q _) cs _) =
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
inferUse u@(Op x _) =
  do logBeginInferUse u
     ty <- find x
     res <- instantiate x ty
     logEndInferUse u res
     return res
inferUse app@(App f xs _) =
  do logBeginInferUse app
     ty <- inferUse f
     res <- discriminate ty
     logEndInferUse app res
     return res
  where -- Check typings of x_i for port p_i
        checkArgs :: [Port Desugared] -> [Tm Desugared] -> Contextual ()
        checkArgs ps xs = mapM_ (uncurry checkArg) (zip ps xs)

        -- Check typing tm: ty in ambient [adj]
        checkArg :: Port Desugared -> Tm Desugared -> Contextual ()
        checkArg (Port adj ty _) tm = inAmbient adj (checkTm tm ty)

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
        discriminate ty@(SCTy (CType ps (Peg ab ty' _) _) _) =
        -- {p_1 -> ... p_n -> [ab] ty'}
          do amb <- getAmbient
             unifyAb amb ab   -- require [amb] = [ab]
             checkArgs ps xs
             return ty'
        discriminate ty@(FTVar y a) =
          do mty <- findFTVar y  -- find definition of y in context
             case mty of
               Nothing -> -- 2.1)
                 -- TODO: check that this is correct
                 do addMark
                    amb <- getAmbient
                    ps <- mapM (\_ -> freshPort "X" a) xs
                    q@(Peg ab ty' _)  <- freshPegWithAb amb "Y" a
                    unify ty (SCTy (CType ps q a) a)
                    return ty'
                 -- errTy ty
               Just ty' -> discriminate ty' -- 2.2)
        discriminate ty = errTy ty

        -- TODO: tidy.
        -- We don't need to report an error here, but rather generate
        -- appropriate fresh type variables as above.
        errTy ty = throwError $
                   "application (" ++ show (App f xs (Desugared Generated)) ++
                   "): expected suspended computation but got " ++
                   (show $ ppVType ty)

-- 2nd major TC function: Check that term (construction) has given type
checkTm :: Tm Desugared -> VType Desugared -> Contextual ()
checkTm (SC sc _) ty = checkSComp sc ty          -- Thunk rule
checkTm (StrTm _ a) ty = unify (desugaredStrTy a) ty
checkTm (IntTm _ a) ty = unify (IntTy a) ty
checkTm (CharTm _ a) ty = unify (CharTy a) ty
checkTm (TmSeq tm1 tm2 a) ty =
  -- create dummy mvar s.t. any type of tm1 can be unified with it
  do ftvar <- freshMVar "seq"
     checkTm tm1 (FTVar ftvar a)
     checkTm tm2 ty
checkTm (Use u a) t = do s <- inferUse u         -- Switch rule
                         unify t s
checkTm (DCon (DataCon k xs _) a) ty =           -- Data rule
  do (dt, args, ts) <- getCtr k
--    data dt arg_1 ... arg_m = k t_1 ... t_n | ...
     addMark
     -- prepare flexible ty vars and ty args
     args' <- mapM (makeFlexibleTyArg []) args
     ts' <- mapM (makeFlexible []) ts
     unify ty (DTTy dt args' a)
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
checkSComp (SComp xs _) (SCTy (CType ps q _) _) =
  mapM_ (\cls -> checkCls cls ps q) xs
checkSComp (SComp xs a) ty = mapM_ (checkCls' ty) xs
  where checkCls' :: VType Desugared -> Clause Desugared -> Contextual ()
        checkCls' ty cls@(Cls pats tm a) =
          do pushMarkCtx
             ps <- mapM (\_ -> freshPort "X" a) pats
             q <- freshPeg "" "X" a
             -- {p_1 -> ... -> p_n -> q} for fresh flex. var.s ps, q
             checkCls cls ps q                -- assign these variables
             unify ty (SCTy (CType ps q a) a) -- unify with resulting ty
             purgeMarks

-- create port <i>X for fresh X
freshPort :: Id -> Desugared -> Contextual (Port Desugared)
freshPort x a = do ty <- FTVar <$> freshMVar x <*> pure a
                   return $ Port (Adj (ItfMap M.empty a) a) ty a

-- create peg [E]Y for fresh E, Y
freshPeg :: Id -> Id -> Desugared -> Contextual (Peg Desugared)
freshPeg x y a = do v <- AbFVar <$> freshMVar x <*> pure a
                    ty <- FTVar <$> freshMVar y <*> pure a
                    return $ Peg (Ab v (ItfMap M.empty a) a) ty a

-- create peg [ab]X for given [ab], fresh X
freshPegWithAb :: Ab Desugared -> Id -> Desugared -> Contextual (Peg Desugared)
freshPegWithAb ab x a = do ty <- FTVar <$> freshMVar x <*> pure a
                           return $ Peg ab ty a

-- Check that given clause has given susp. comp. type (ports, peg)
checkCls :: Clause Desugared -> [Port Desugared] -> Peg Desugared ->
           Contextual ()
checkCls cls@(Cls pats tm _) ports (Peg ab ty _)
-- type:     port_1 -> ... -> port_n -> [ab]ty
-- clause:   pat_1     ...    pat_n  =  tm
  | length pats == length ports =
     do pushMarkCtx
        putAmbient ab  -- restrict ambient ability
        bs <- fmap concat $ mapM (uncurry checkPat) (zip pats ports)
        -- Bring any bindings in to scope for checking the term then purge the
        -- marks (and suffixes) in the context created for this clause.
        case null bs of
          True ->  do -- Just purge marks
                      checkTm tm ty
                      purgeMarks
          False -> do -- Push all bindings to context, then check tm, then remove bindings,
                      -- finally purge marks.
                      foldl1 (.) (map (uncurry inScope) bs) $ checkTm tm ty
                      purgeMarks
  | otherwise = throwError $ errorTCPatternPortMismatch cls

-- Check that given pattern matches given port
checkPat :: Pattern Desugared -> Port Desugared -> Contextual [TermBinding]
checkPat (VPat vp _) (Port _ ty _) = checkVPat vp ty
checkPat (CmdPat cmd xs g a) (Port adj ty b) =
-- interface itf q_1 ... q_m =
--   cmd r_1 ... r_l: t_1 -> ... -> t_n -> y | ...

-- port:     <itf p_1 ... p_m> ty
-- pattern:  <cmd x_1 ... x_n -> g>
  do (itf, qs, rs, ts, y) <- getCmd cmd
     mps <- lkpItf itf (plus (Ab (EmpAb b) (ItfMap M.empty a) b) adj) -- how is itf instantiated in adj?
     case mps of
       Nothing -> throwError $ errorTCCmdNotFoundInAdj cmd adj
       Just ps -> do addMark
                     -- Flexible ty vars (corresponding to qs)
                     nonFlexs <- getCmdTyVars cmd
                     -- Localise qs, bind them to their instantiation
                     -- (according to adjustment) and localise their occurences
                     -- in ts, y
                     qs' <- mapM (makeFlexibleTyArg nonFlexs) qs
                     ts' <- mapM (makeFlexible nonFlexs) ts
                     y' <- makeFlexible nonFlexs y
                     mapM (uncurry unifyTyArg) (zip ps qs')
                     -- Check command patterns against spec. in interface def.
                     bs <- fmap concat $ mapM (uncurry checkVPat) (zip xs ts')
                     kty <- contType y' adj ty a -- type of continuation:  {y' -> [adj + currentAmb]ty}
                     -- bindings: continuation + patterns
                     return ((Mono g a, kty) : bs)
checkPat (ThkPat x a) (Port adj ty b) =
-- pattern:  x
  do amb <- getAmbient
     return $ [(Mono x a, SCTy (CType [] (Peg (plus amb adj) ty b) b) b)]

-- continuation type
contType :: VType Desugared -> Adj Desugared -> VType Desugared -> Desugared ->
            Contextual (VType Desugared)
contType x adj y a =
  do amb <- getAmbient
     return $ SCTy (CType [Port idAdjDesug x a] (Peg (plus amb adj) y a) a) a

-- Check that a value pattern has a given type (corresponding to rules)
-- Return its bindings (id -> value type)
checkVPat :: ValuePat Desugared -> VType Desugared -> Contextual [TermBinding]
checkVPat (VarPat x a) ty = return [(Mono x a, ty)]  -- P-Var rule
--         x
checkVPat (DataPat k ps a) ty =                      -- P-Data rule
--         k p_1 .. p_n
  do (dt, args, ts) <- getCtr k
--   data dt arg_1 .. arg_m = k t_1 .. t_n | ...
     addMark
     args' <- mapM (makeFlexibleTyArg []) args
     ts' <- mapM (makeFlexible []) ts
     unify ty (DTTy dt args' a)
     bs <- fmap concat $ mapM (uncurry checkVPat) (zip ps ts')
     return bs
checkVPat (CharPat _ a) ty = unify ty (CharTy a) >> return []
checkVPat (StrPat _ a) ty = unify ty (desugaredStrTy a) >> return []
checkVPat (IntPat _ a) ty = unify ty (IntTy a) >> return []
-- checkVPat p ty = throwError $ "failed to match value pattern " ++
--                  (show p) ++ " with type " ++ (show ty)

-- Given a list of ids and a type as input, any rigid (val/eff) ty var
-- contained in ty which does *not* belong to the list is made flexible.
-- The context is thereby extended.
-- Case distinction over contained rigid (val/eff) ty var:
-- 1) it is already part of current locality (up to the Mark)
--    -> return its occuring name
-- 2) it is not part of current locality
--    -> create fresh name in context and return
makeFlexible :: [Id] -> VType Desugared -> Contextual (VType Desugared)
makeFlexible flexs (DTTy id ts a) = DTTy id <$> mapM (makeFlexibleTyArg flexs) ts <*> pure a
makeFlexible flexs (SCTy cty a) = SCTy <$> makeFlexibleCType flexs cty <*> pure a
makeFlexible flexs (RTVar x a) | not (x `elem` flexs) = FTVar <$> (getContext >>= find') <*> pure a
-- find' either creates a new FlexMVar in current locality or identifies the one
-- already existing
  where find' BEmp = freshMVar x
        find' (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' (es :< Mark) = freshMVar x  -- only search in current locality
        find' (es :< _) = find' es
makeFlexible flexs ty = return ty

makeFlexibleAb :: [Id] -> Ab Desugared -> Contextual (Ab Desugared)
makeFlexibleAb flexs (Ab v (ItfMap m _) a) = case v of
  AbRVar x b -> do v' <- (if not (x `elem` flexs) then (AbFVar <$> (getContext >>= (find' x)) <*> pure b) else return $ AbRVar x b)
                   m' <- mapM (mapM (makeFlexibleTyArg flexs)) m
                   return $ Ab v' (ItfMap m' a) a
  _ ->          do m' <- mapM (mapM (makeFlexibleTyArg flexs)) m
                   return $ Ab v (ItfMap m' a) a
-- find' either creates a new FlexMVar in current locality or identifies the one
-- already existing
  where find' x BEmp = freshMVar x
        find' x (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' x (es :< Mark) = freshMVar x
        find' x (es :< _) = find' x es

makeFlexibleTyArg :: [Id] -> TyArg Desugared -> Contextual (TyArg Desugared)
makeFlexibleTyArg flexs (VArg t a)  = VArg <$> makeFlexible flexs t <*> pure a
makeFlexibleTyArg flexs (EArg ab a) = EArg <$> makeFlexibleAb flexs ab <*> pure a

makeFlexibleAdj :: [Id] -> Adj Desugared -> Contextual (Adj Desugared)
makeFlexibleAdj flexs (Adj (ItfMap m _) a) = do m' <- mapM (mapM (makeFlexibleTyArg flexs)) m
                                                return $ Adj (ItfMap m' a) a

makeFlexibleCType :: [Id] -> CType Desugared -> Contextual (CType Desugared)
makeFlexibleCType flexs (CType ps q a) = CType <$>
                                         mapM (makeFlexiblePort flexs) ps <*>
                                         makeFlexiblePeg flexs q <*>
                                         pure a

makeFlexiblePeg :: [Id] -> Peg Desugared -> Contextual (Peg Desugared)
makeFlexiblePeg flexs (Peg ab ty a) = Peg <$>
                                      makeFlexibleAb flexs ab <*>
                                      makeFlexible flexs ty <*>
                                      pure a

makeFlexiblePort :: [Id] -> Port Desugared -> Contextual (Port Desugared)
makeFlexiblePort flexs (Port adj ty a) = Port <$>
                                         makeFlexibleAdj flexs adj <*>
                                         makeFlexible flexs ty <*>
                                         pure a

-- helpers

getCtr :: Id -> Contextual (Id,[TyArg Desugared],[VType Desugared])
getCtr k = get >>= \s -> case M.lookup k (ctrMap s) of
  Nothing -> throwError $ errorTCNotACtr k
  Just (dt, ts, xs) -> return (dt, ts, xs)
