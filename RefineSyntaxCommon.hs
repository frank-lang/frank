-- Definitions used during refinement phase
module RefineSyntaxCommon where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

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
type DTMap = M.Map Id [(Id, Kind)]                      -- dt-id     -> [ty-vars]
type IFMap = M.Map Id [(Id, Kind)]                      -- itf-id    -> [ty-vars]
type IFAliasesMap = M.Map Id ([(Id, Kind)], ItfMap Raw) -- itf-al-id -> ([ty-vars], itf's -> itf-instant's)

data TopLevelCtxt = Interface | InterfaceAlias | Datatype | Handler
  deriving (Show, Eq)

data RState = MkRState { interfaces :: IFMap
                       , interfaceAliases :: IFAliasesMap
                       , datatypes :: DTMap
                       , handlers :: [IPair]              -- handler Id -> # of arguments
                       , ctrs :: [IPair]                  -- constructor Id -> # of arguments
                       , cmds :: [IPair]                  -- command Id -> # of arguments
                       , program :: Prog Refined          -- LC: what is this for?
                       , tmap :: TVarMap                  -- type var Id ->   VType Raw     type vars of current context
                       , evmap :: EVarSet                 -- effect var Id                  effect vars of current context
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

putRItfAliases :: IFAliasesMap -> Refine ()
putRItfAliases xs = do s <- getRState
                       putRState $ s {interfaceAliases = xs }

getRItfAliases :: Refine (IFAliasesMap)
getRItfAliases = do s <- getRState
                    return $ interfaceAliases s

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

{- Helper functions -}

isHdrCtxt :: Maybe TopLevelCtxt -> Bool
isHdrCtxt (Just Handler) = True
isHdrCtxt _              = False
