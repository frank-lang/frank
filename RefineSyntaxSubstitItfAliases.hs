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

import Debug.Trace

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
        Just (ps, itfMap) ->
--               1) interface x p_1 ... p_n     = [itf_i p_i1 ... p_ik, ...]
--            or 2) interface x p_1 ... p_n [£] = [itf_i p_i1 ... p_ik, ...]
--                  and [£] has been explicitly added before
--                                if 2), set t_{n+1} := [£]
          do let ts' = if length ps == length ts + 1 &&
                          (snd (ps !! length ts) == ET) then
                            ts ++ [EArg (MkAb (MkAbVar "£") M.empty)]
                       else ts
             checkArgs x (length ps) (length ts')
             let subst = zip ps ts'
             -- replace   x ts
             --      by   [x_1 ts_1', ..., x_n ts_n']
             -- where ts_i' has been acted upon by subst
             xs <- mapM (substitInTyArgs subst) (M.toList itfMap)
             -- recursively replace itf als in   x_1, ..., x_n
             --                       yielding   [[x_11 x_11_ts, ...], ...]
             xss <- mapM (substitItfAls' (x:visited)) xs
             return $ concat xss
    else throwError $ "interface alias " ++ show x ++ " is defined in terms of itself (cycle)"

type Subst = [((Id, Kind), TyArg Raw)]

substLookupVT :: Subst -> Id -> Maybe (VType Raw)
substLookupVT subst x = case find (\((x', k), y) -> x' == x && k == VT) subst of
  Just (_, VArg ty) -> Just ty
  _                 -> Nothing

substLookupET :: Subst -> Id -> Maybe (Ab Raw)
substLookupET subst x = case find (\((x', k), y) -> x' == x && k == ET) subst of
  Just (_, EArg ab) -> Just ab
  _                 -> Nothing

substitInTyArgs :: Subst -> (Id, [TyArg Raw]) -> Refine (Id, [TyArg Raw])
substitInTyArgs subst (x, ts) = do ts' <- mapM (substitInTyArg subst) ts
                                   return (x, ts')
-- Replace (x, VT/ET) by ty-arg
substitInTyArg :: Subst -> TyArg Raw -> Refine (TyArg Raw)
substitInTyArg subst (VArg ty) = VArg <$> (substitInVType subst ty)
substitInTyArg subst (EArg ab) = EArg <$> (substitInAb subst ab)

substitInVType :: Subst -> VType Raw -> Refine (VType Raw)
substitInVType subst (MkDTTy x ts) = do
  dtm <- getRDTs
  tmap <- getTMap
  ctx <- getTopLevelCtxt
  case (not (M.member x dtm) && -- Check if id really is type variable
        null ts &&
        (isHdrCtxt ctx ||
         M.member x tmap), substLookupVT subst x) of -- if so, then substitute
    (True, Just y) -> return y
    _              -> do ts' <- mapM (substitInTyArg subst) ts
                         return $ MkDTTy x ts'
substitInVType subst (MkSCTy ty) = substitInCType subst ty >>= return . MkSCTy
substitInVType subst (MkTVar x) = case substLookupVT subst x of
  Just y -> return y
  _      -> return $ MkTVar x
substitInVType subst ty = return ty  -- MkStringTy, MkIntTy, MkCharTy

substitInCType :: Subst -> CType Raw -> Refine (CType Raw)
substitInCType subst (MkCType ports peg) = do ports' <- mapM (substitInPort subst) ports
                                              peg' <- substitInPeg subst peg
                                              return $ MkCType ports' peg'

substitInPort :: Subst -> Port Raw -> Refine (Port Raw)
substitInPort subst (MkPort adj ty) = do adj' <- substitInAdj subst adj
                                         ty' <- substitInVType subst ty
                                         return $ MkPort adj' ty'

substitInPeg :: Subst -> Peg Raw -> Refine (Peg Raw)
substitInPeg subst (MkPeg ab ty) = do ab' <- substitInAb subst ab
                                      ty' <- substitInVType subst ty
                                      return $ MkPeg ab' ty'

substitInAb :: Subst -> Ab Raw -> Refine (Ab Raw)
substitInAb subst a = return a

substitInAdj :: Subst -> Adj Raw -> Refine (Adj Raw)
substitInAdj subst (MkAdj m) = substitInItfMap subst m >>= return . MkAdj

substitInItfMap :: Subst -> ItfMap Raw -> Refine (ItfMap Raw)
substitInItfMap subst itfMap = do M.fromList <$> mapM (substitInTyArgs subst) (M.toList itfMap)
