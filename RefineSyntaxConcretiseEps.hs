-- Making implicit [£] explicit in data type, interface and interface alias
-- definitions
module RefineSyntaxConcretiseEps (concretiseEps, concretiseEpsArg) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import BwdFwd
import Syntax

-- Node container for the graph algorithm
data Node = DtNode (DataT Raw) | ItfNode (Itf Raw) | ItfAlNode (ItfAlias Raw)
  deriving (Show, Eq)

-- Used as a result of inspecting a node on whether it has an
-- (implicit/explicit) [£]
data HasEps = HasEps |           -- "Yes" with certainty
              HasEpsIfAny [Node] -- "Yes" if any of the given nodes (definitions)
                                 --       have implicit [£]
                                 -- (n.b. HasEpsIfAny [] corresponds to "No")
  deriving (Show, Eq)

-- Given data type, interface and interface alias def's, determine which of them
-- carry an implicit or explicit [£] eff var. As the def's may depend on each
-- other, we consider each def. a node and model the dependencies as a
-- dependency graph.
-- A node will be decided either positive (i.e. carries [£]) or
-- negative (i.e. no [£]). Whenever a node reaches a positive one, it is also
-- decided positive (i.e. any contained subtype requiring [£] induces
-- [£] for the parent).
-- Finally, all definitions that are decided to have [£], but do not yet
-- explicitly have it, are added an additional [£] eff var.
concretiseEps :: [DataT Raw] -> [Itf Raw] -> [ItfAlias Raw] -> ([DataT Raw], [Itf Raw], [ItfAlias Raw])
concretiseEps dts itfs itfAls =
  let posNodes = decideGraph (nodes, [], [])
      posDts    = [getId x | DtNode x    <- posNodes]
      posItfs   = [getId x | ItfNode x   <- posNodes]
      posItfAls = [getId x | ItfAlNode x <- posNodes] in
  (map (concretiseEpsInDataT posDts) dts,
   map (concretiseEpsInItf   posItfs) itfs,
   map (concretiseEpsInItfAl posItfAls) itfAls)
  where

  nodes :: [Node]
  nodes = map DtNode dts ++ map ItfNode itfs ++ map ItfAlNode itfAls

  resolveDataId :: Id -> Maybe Node
  resolveDataId x = case [DtNode d | DtNode d <- nodes, getId d == x] of
                      [x] -> Just x
                      _   -> Nothing
  -- TODO: LC: Use Map datastructure

  resolveItfId :: Id -> Maybe Node
  resolveItfId x = case ([i | ItfNode i <- nodes, getId i == x],
                         [i | ItfAlNode i <- nodes, getId i == x]) of
                     ([i], []) -> Just $ ItfNode i
                     ([], [i]) -> Just $ ItfAlNode i
                     _ -> Nothing

  -- Given graph (undecided-nodes, positive-nodes, negative-nodes), decide
  -- subgraphs as long as there are unvisited nodes. Finally (base case),
  -- return positive nodes.
  decideGraph :: ([Node], [Node], [Node]) -> [Node]
  decideGraph ([],   pos, _  ) = pos
  decideGraph (x:xr, pos, neg) = decideGraph $ runIdentity $ execStateT (decideSubgraph x) (xr, pos, neg)

  -- Given graph (passed as state, same as for decideGraph) and a starting
  -- node x (already excluded from the graph), visit the whole subgraph
  -- reachable from x and thereby decide each node.
  -- To avoid cycles, x must always be excluded from graph.
  -- Method: 1) Try to decide x on its own. Either:
  --            (1), (2) Already decided
  --            (3), (4) Decidable without dependencies
  --         2) If x's decision is dependent on neighbours' ones, visit all
  --            and recursively decide them, too. Either:
  --            (5)(i)  Some neighbour y is decided pos.  => x is pos.
  --            (5)(ii) All neighbours y are decided neg. => x is neg.
  decideSubgraph :: Node -> State ([Node], [Node], [Node]) Bool
  decideSubgraph x = do
    (xs, pos, neg) <- get
    if        x `elem` pos then return True      -- (1)
    else if   x `elem` neg then return False     -- (2)
    else case hasEpsNode x of
      HasEps          -> do put (xs, x:pos, neg) -- (3)
                            return True
      HasEpsIfAny nodes ->
        let neighbours = (nub nodes) `intersect` (xs ++ pos ++ neg) in
        do dec <- foldl (\dec y -> do -- Exclude neighbour from graph
                                      (xs', pos', neg') <- get
                                      put (xs' \\ [y], pos', neg')
                                      d  <- dec
                                      d' <- decideSubgraph y
                                      -- Once pos. y found, result stays pos.
                                      return $ d || d')
                        (return False)           -- (4) (no neighbours)
                        neighbours
           (xs', pos', neg') <- get
           if dec then put (xs', x:pos', neg')   -- (5)(i)
                  else put (xs', pos', x:neg')   -- (5)(ii)
           return dec

  {- hasEpsX functions examine an instance of X and determine whether it
     1) has an [£] for sure or
     2) has an [£] depending on other definitions

     The tvs parameter hold the locally introduced value type variables. It
     serves the following purpose: If an identifier is encountered, we cannot be
     sure if it was correctly determined as either data type or local type
     variable. This is the exact same issue to deal with as in refineVType,
     now in hasEpsVType -}

  hasEpsNode :: Node -> HasEps
  hasEpsNode node = case node of (DtNode dt) -> hasEpsDataT dt
                                 (ItfNode itf) -> hasEpsItf itf
                                 (ItfAlNode itfAl) -> hasEpsItfAl itfAl

  hasEpsDataT :: DataT Raw -> HasEps
  hasEpsDataT (DT _ ps ctrs a) = if ("£", ET) `elem` ps then HasEps
                                 else let tvs = [x | (x, VT) <- ps] in
                                      anyHasEps (map (hasEpsCtr tvs) ctrs)

  hasEpsItf :: Itf Raw -> HasEps
  hasEpsItf (Itf _ ps cmds a) = if ("£", ET) `elem` ps then HasEps
                                else let tvs = [x | (x, VT) <- ps] in
                                     anyHasEps (map (hasEpsCmd tvs) cmds)

  hasEpsItfAl :: ItfAlias Raw -> HasEps
  hasEpsItfAl (ItfAlias _ ps itfMap a) = if ("£", ET) `elem` ps then HasEps
                                         else let tvs = [x | (x, VT) <- ps] in
                                              hasEpsItfMap tvs itfMap

  hasEpsCmd :: [Id] -> Cmd Raw -> HasEps
  hasEpsCmd tvs (Cmd _ ps ts t a) = let tvs' = tvs ++ [x | (x, VT) <- ps] in
                                    anyHasEps $ map (hasEpsVType tvs') ts ++ [hasEpsVType tvs' t]

  hasEpsCtr :: [Id] -> Ctr Raw -> HasEps
  hasEpsCtr tvs (Ctr _ ts a) = anyHasEps (map (hasEpsVType tvs) ts)

  hasEpsVType :: [Id] -> VType Raw -> HasEps
  hasEpsVType tvs (DTTy x ts a) =
    if x `elem` dtIds then hasEpsDTTy tvs x ts                   -- indeed data type
                      else anyHasEps $ map (hasEpsTyArg tvs) ts  -- ... or not (but type var)
    where dtIds = [getId d | DtNode d <- nodes]
  hasEpsVType tvs (SCTy ty a)   = hasEpsCType tvs ty
  hasEpsVType tvs (TVar x a)    = if x `elem` tvs then HasEpsIfAny []      -- indeed type variable
                                                  else hasEpsDTTy tvs x [] -- ... or not (but data type)
  hasEpsVType tvs (StringTy _)  = HasEpsIfAny []
  hasEpsVType tvs (IntTy _)     = HasEpsIfAny []
  hasEpsVType tvs (CharTy _)    = HasEpsIfAny []

  hasEpsDTTy :: [Id] -> Id -> [TyArg Raw] -> HasEps
  hasEpsDTTy tvs x ts =
    -- An datatype x gives only rise to adding an eps if the number of ty
    -- args are exactly as required by x. Thus, if x has an additional
    -- implicit eps, it should be given as an additional parameter here, too
    case resolveDataId x of
      Just x' -> let
        dtHE   = if isDtWithNArgs x' (length ts) then [HasEpsIfAny [x']] else []
        argsHE = map (hasEpsTyArg tvs) ts
        in anyHasEps (dtHE ++ argsHE)
      Nothing -> HasEpsIfAny []
    where isDtWithNArgs :: Node -> Int -> Bool
          isDtWithNArgs (DtNode (DT _ ps _ _)) n = length ps == n


  hasEpsCType :: [Id] -> CType Raw -> HasEps
  hasEpsCType tvs (CType ports peg a) = anyHasEps $ map (hasEpsPort tvs) ports ++ [hasEpsPeg tvs peg]

  hasEpsPort :: [Id] -> Port Raw -> HasEps
  hasEpsPort tvs (Port adj ty a) = anyHasEps [hasEpsAdj tvs adj, hasEpsVType tvs ty]

  hasEpsAdj :: [Id] -> Adj Raw -> HasEps
  hasEpsAdj tvs (Adj itfmap a) = hasEpsItfMap tvs itfmap

  hasEpsPeg :: [Id] -> Peg Raw -> HasEps
  hasEpsPeg tvs (Peg ab ty a) = anyHasEps [hasEpsAb tvs ab, hasEpsVType tvs ty]

  hasEpsAb :: [Id] -> Ab Raw -> HasEps
  hasEpsAb tvs (Ab v m a) = anyHasEps [hasEpsAbMod tvs v, hasEpsItfMap tvs m]

  hasEpsItfMap :: [Id] -> ItfMap Raw -> HasEps
  hasEpsItfMap tvs mp@(ItfMap m _) =
    let -- An interface i gives only rise to adding an eps if the number of ty
        -- args are exactly as required by i. Thus, if i has an additional
        -- implicit eps, it should be given as an additional parameter here, too
        itfsHE = map hasEpsInst (flattenItfMap mp)
        argsHE = (map (hasEpsTyArg tvs) . concat . concatMap bwd2fwd . M.elems) m
    in anyHasEps (itfsHE ++ argsHE)
    where flattenItfMap :: ItfMap t -> [(Id, [TyArg t])]
          flattenItfMap (ItfMap m _) = concat $ map (\(i, insts) -> map (\inst -> (i, inst)) (bwd2fwd insts)) (M.toList m)

          hasEpsInst :: (Id, [TyArg Raw]) -> HasEps
          hasEpsInst (i, inst) = case resolveItfId i of
            Just x -> if isItfWithNArgs x (length inst) then HasEpsIfAny [x] else HasEpsIfAny []
            _ -> HasEpsIfAny []

          isItfWithNArgs :: Node -> Int -> Bool
          isItfWithNArgs (ItfNode (Itf _ ps _ _))        n = length ps == n
          isItfWithNArgs (ItfAlNode (ItfAlias _ ps _ _)) n = length ps == n

  hasEpsAbMod :: [Id] -> AbMod Raw -> HasEps
  hasEpsAbMod tvs (EmpAb _)     = HasEpsIfAny []
  hasEpsAbMod tvs (AbVar "£" _) = HasEps
  hasEpsAbMod tvs (AbVar _ _)   = HasEpsIfAny []

  hasEpsTyArg :: [Id] -> TyArg Raw -> HasEps
  hasEpsTyArg tvs (VArg t _)  = hasEpsVType tvs t
  hasEpsTyArg tvs (EArg ab _) = hasEpsAb tvs ab

concretiseEpsInDataT :: [Id] -> DataT Raw -> DataT Raw
concretiseEpsInDataT posIds (DT dt ps ctrs a) = DT dt ps' ctrs a where
  ps' = if ("£", ET) `notElem` ps && dt `elem` posIds then ps ++ [("£", ET)] else ps

concretiseEpsInItf :: [Id] -> Itf Raw -> Itf Raw
concretiseEpsInItf posIds (Itf itf ps cmds a) = Itf itf ps' cmds a where
  ps' = if ("£", ET) `notElem` ps && itf `elem` posIds then ps ++ [("£", ET)] else ps

concretiseEpsInItfAl :: [Id] -> ItfAlias Raw -> ItfAlias Raw
concretiseEpsInItfAl posIds (ItfAlias itfAl ps itfMap a) = ItfAlias itfAl ps' itfMap a where
  ps' = if ("£", ET) `notElem` ps && itfAl `elem` posIds then ps ++ [("£", ET)] else ps

{- This function adds an implicit [£|] *argument* if the type signature
   requires it. -}

concretiseEpsArg :: [(Id, Kind)] -> [TyArg Raw] -> Raw -> [TyArg Raw]
concretiseEpsArg ps ts a = if length ps == length ts + 1 &&
                              (snd (ps !! length ts) == ET)
                           then ts ++ [EArg (Ab (AbVar "£" a) (ItfMap M.empty a) a) a]
                           else ts

{- Helper functions -}

-- A variant of the any-operator for HasEps results
anyHasEps :: [HasEps] -> HasEps
anyHasEps xs = if HasEps `elem` xs then HasEps
               else HasEpsIfAny (concat [ids | HasEpsIfAny ids <- xs])
