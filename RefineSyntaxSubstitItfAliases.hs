{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

-- Recursively substitute an interface alias occurrence by its definition
module RefineSyntaxSubstitItfAliases (substitItfAls) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax
import RefineSyntaxCommon
import Debug

-- Given an occurrence of interface instantiation x t_1 ... t_n, determine
-- whether it is an interface alias and if so, recursively substitute
substitItfAls :: (Id, [TyArg Raw]) -> Refine [(Id, [TyArg Raw])]
substitItfAls = substitItfAls' [] where
  substitItfAls' :: [Id] -> (Id, [TyArg Raw]) -> Refine [(Id, [TyArg Raw])]
  substitItfAls' visited (x, ts) = do
    itfAls <- getRItfAliases
    if not (x `elem` visited) then
      case M.lookup x itfAls of
        Nothing -> return [(x, ts)]
        Just (ps, ItfMap itfMap _) ->
--            1) interface x p_1 ... p_n     = [itf_i p_i1 ... p_ik, ...]
--         or 2) interface x p_1 ... p_n [£] = [itf_i p_i1 ... p_ik, ...]
--               and [£] has been explicitly added before
--                                if 2), set t_{n+1} := [£]
          do let ts' = if length ps == length ts + 1 &&
                          (snd (ps !! length ts) == ET)
                       then let a = Raw Implicit in
                            ts ++ [EArg (Ab (AbVar "£" a) (ItfMap M.empty a) a) a]
                       else ts
             checkArgs x (length ps) (length ts') (Raw Generated) -- TODO: LC: Fix annotation
             let subst = zip ps ts'
             -- replace   x ts
             --      by   [x_1 ts_1', ..., x_n ts_n']
             -- where ts_i' has been acted upon by subst
             xs <- mapM (substitInTyArgs subst) (M.toList itfMap)
             -- recursively replace itf als in   x_1, ..., x_n
             --                       yielding   [[x_11 x_11_ts, ...], ...]
             xss <- mapM (substitItfAls' (x:visited)) xs
             return $ concat xss
    else throwError $ errorRefItfAlCycle x

type Subst = [((Id, Kind), TyArg Raw)]

substLookupVT :: Subst -> Id -> Maybe (VType Raw)
substLookupVT subst x = case find (\((x', k), y) -> x' == x && k == VT) subst of
  Just (_, VArg ty a) -> Just ty
  _                    -> Nothing

substLookupET :: Subst -> Id -> Maybe (Ab Raw)
substLookupET subst x = case find (\((x', k), y) -> x' == x && k == ET) subst of
  Just (_, EArg ab a) -> Just ab
  _                    -> Nothing

substitInTyArgs :: Subst -> (Id, [TyArg Raw]) -> Refine (Id, [TyArg Raw])
substitInTyArgs subst (x, ts) = do ts' <- mapM (substitInTyArg subst) ts
                                   return (x, ts')
-- Replace (x, VT/ET) by ty-arg
substitInTyArg :: Subst -> TyArg Raw -> Refine (TyArg Raw)
substitInTyArg subst (VArg ty a) = VArg <$> (substitInVType subst ty) <*> pure a
substitInTyArg subst (EArg ab a) = EArg <$> (substitInAb subst ab) <*> pure a

substitInVType :: Subst -> VType Raw -> Refine (VType Raw)
substitInVType subst (DTTy x ts a) = do
  dtm <- getRDTs
  tmap <- getTMap
  ctx <- getTopLevelCtxt
  case (not (M.member x dtm) && -- Check if id really is type variable
        null ts &&
        (isHdrCtxt ctx ||
         M.member x tmap), substLookupVT subst x) of -- if so, then substitute
    (True, Just y) -> return $ y     -- TODO: LC: Right annotation assigned?
    _              -> do ts' <- mapM (substitInTyArg subst) ts
                         return $ DTTy x ts' a
substitInVType subst (SCTy ty a) = do cty <- substitInCType subst ty
                                      return $ SCTy cty a
substitInVType subst (TVar x a) =
  case substLookupVT subst x of
    Just y -> return $ y   -- TODO: LC: Right annotation assigned?
    _      -> return $ TVar x a
substitInVType subst ty = return ty  -- MkStringTy, MkIntTy, MkCharTy

substitInCType :: Subst -> CType Raw -> Refine (CType Raw)
substitInCType subst (CType ports peg a) = do ports' <- mapM (substitInPort subst) ports
                                              peg' <- substitInPeg subst peg
                                              return $ CType ports' peg' a

substitInPort :: Subst -> Port Raw -> Refine (Port Raw)
substitInPort subst (Port adj ty a) = do adj' <- substitInAdj subst adj
                                         ty' <- substitInVType subst ty
                                         return $ Port adj' ty' a

substitInPeg :: Subst -> Peg Raw -> Refine (Peg Raw)
substitInPeg subst (Peg ab ty a) = do ab' <- substitInAb subst ab
                                      ty' <- substitInVType subst ty
                                      return $ Peg ab' ty' a

substitInAb :: Subst -> Ab Raw -> Refine (Ab Raw)
substitInAb subst a = return a

substitInAdj :: Subst -> Adj Raw -> Refine (Adj Raw)
substitInAdj subst (Adj m a) = do itfMap <- substitInItfMap subst m
                                  return $ Adj itfMap a

substitInItfMap :: Subst -> ItfMap Raw -> Refine (ItfMap Raw)
substitInItfMap subst (ItfMap itfMap a) = do (ItfMap . M.fromList) <$> mapM (substitInTyArgs subst) (M.toList itfMap) <*> pure a

-- helpers

checkArgs :: Id -> Int -> Int -> Raw -> Refine ()
checkArgs x exp act a =
  if exp /= act then
    throwError $ errorRefNumberOfArguments x exp act a
  else return ()
