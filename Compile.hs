{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- Compile Frank to Shonky
module Compile where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax
import qualified Shonky.Syntax as S

import Debug.Trace
import Debug

import BwdFwd

testShonky =
  unlines $
  [ "evalstate(,get put):"
  , "evalstate(x,y) -> y,"
  , "evalstate(x,{'get() -> k}) -> evalstate(x,k(x)),"
  , "evalstate(x,{'put(y) -> k}) -> evalstate(y,k([]))"
  , "main():"
  , "main() -> evalstate([|hello|], 'put(['get(),[|world|]]);'get())"]

type Compile = State CState

type ItfCmdMap = M.Map Id [Id]

data CState = MkCState { imap :: ItfCmdMap
                       , atoms :: S.Set String}

initCState :: CState
initCState = MkCState M.empty S.empty

getCState :: Compile CState
getCState = get

putCState :: CState -> Compile ()
putCState = put

getCCmds :: Id -> Compile [Id]
getCCmds itf = do s <- getCState
                  return $ M.findWithDefault [] itf (imap s)

addAtom :: Id -> Compile ()
addAtom id = do s <- getCState
                putCState $ s { atoms = S.insert id (atoms s) }

isAtom :: Id -> Compile Bool
isAtom id = do s <- getCState
               return $ S.member id (atoms s)

compileToFile :: (NotRaw a, Show a, HasSource a) => Prog a -> String -> IO ()
compileToFile p dst = writeFile (dst ++ ".uf") (show $ S.ppProg $ compile p)

compile :: (NotRaw a, Show a, HasSource a) => Prog a -> [S.Def S.Exp]
compile (MkProg xs) = res
  where res = reverse $ evalState (compile' xs) st
        st = initialiseItfMap initCState [i | ItfTm i _ <- xs]

compile' :: (NotRaw a, Show a, HasSource a) => [TopTm a] -> Compile [S.Def S.Exp]
compile' xs = do liftM concat $ mapM compileTopTm xs

initialiseItfMap :: (NotRaw a, Show a, HasSource a) => CState -> [Itf a] -> CState
initialiseItfMap st xs = st { imap = foldl f (imap st) xs }
  where f m (Itf id _ xs _) = foldl (ins id) m xs
        ins itf m (Cmd cmd _ _ _ _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTm :: (NotRaw a, Show a, HasSource a) => TopTm a -> Compile [S.Def S.Exp]
compileTopTm (DataTm x _) = compileDatatype x
compileTopTm (DefTm x@(Def id _ _ _) _) =
  if isBuiltin id then return []  else do def <- compileMHDef x
                                          return $ [def]
compileTopTm _ = return [] -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: (NotRaw a, Show a, HasSource a) => DataT a -> Compile [S.Def S.Exp]
compileDatatype (DT _ _ xs _) = mapM compileCtr xs

-- nonNullary :: [Ctr a] -> Compile [Ctr a]
-- nonNullary ((MkCtr id []) : xs) = do addAtom id
--                                      nonNullary xs
-- nonNullary (x : xs) = do xs' <- nonNullary xs
--                          return $ x : xs'
-- nonNullary [] = return []

compileCtr :: (NotRaw a, Show a, HasSource a) => Ctr a -> Compile (S.Def S.Exp)
compileCtr (Ctr id [] _) = return $ S.DF id [] [([], S.EA id S.:& S.EA "")]
compileCtr (Ctr id ts _) =
  let f x n = x ++ (show n) in
  let xs = take (length ts) $ repeat "x" in
  let xs' = zipWith f xs [1..] in
  let args = map (S.PV . S.VPV) xs' in
  let e = foldr1 (S.:&) $ (S.EA id) : (map S.EV xs' ++ [S.EA ""]) in
  return $ S.DF id [] [(args, e)]

-- use the type to generate the signature of commands handled
-- generate a clause 1-to-1 correspondence
compileMHDef :: (NotRaw a, Show a, HasSource a) => MHDef a -> Compile (S.Def S.Exp)
compileMHDef (Def id ty xs _) = do xs' <- mapM compileClause xs
                                   tyRep <- compileCType ty
                                   return $ S.DF id tyRep xs'

compileCType :: (NotRaw a, Show a, HasSource a) => CType a -> Compile [[String]]
compileCType (CType xs _ _) = mapM compilePort xs

compilePort :: (NotRaw a, Show a, HasSource a) => Port a -> Compile [String]
compilePort (Port adj _ _) = compileAdj adj

compileAdj :: (NotRaw a, Show a, HasSource a) => Adj a -> Compile [String]
compileAdj (Adj a@(ItfMap m _) _) =
  do let m' = M.mapWithKey (\i insts ->
                             replicate ((length . bwd2fwd) insts) i) m
     cmds <- liftM concat $ mapM getCCmds (concat (M.elems m'))
     return cmds

compileClause :: (NotRaw a, Show a, HasSource a) => Clause a -> Compile ([S.Pat], S.Exp)
compileClause (Cls ps tm _) = do ps' <- mapM compilePattern ps
                                 e <- compileTm tm
                                 return (ps', e)

compilePattern :: (NotRaw a, Show a, HasSource a) => Pattern a -> Compile S.Pat
compilePattern (VPat x _) = S.PV <$> compileVPat x
compilePattern c@(CmdPat cmd n xs k _) = do xs' <- mapM compileVPat xs
                                            return $ S.PC cmd (toInteger n) xs' k
compilePattern (ThkPat id _) = return $ S.PT id

-- The current version simply represents Frank characters as one
-- character Shonky strings and Frank strings as a Shonky datatype
-- with "cons" and "nil" constructors.

compileVPat :: (NotRaw a, Show a, HasSource a) => ValuePat a -> Compile S.VPat
compileVPat (VarPat id _) = return $ S.VPV id
compileVPat (DataPat id xs _) =
  do case xs of
       []  -> return $ S.VPA id S.:&: S.VPA ""
       xs -> do xs' <- mapM compileVPat xs
                return $ foldr1 (S.:&:) $ (S.VPA id) : (xs' ++ [S.VPA ""])
compileVPat (IntPat n _) = return $ S.VPI n
compileVPat ((StrPat s a) :: ValuePat a) = compileVPat (compileStrPat s) where
  compileStrPat :: String -> ValuePat a
  compileStrPat []     = DataPat "nil" [] a
  compileStrPat (c:cs) = DataPat "cons" [CharPat c a, compileStrPat cs] a
compileVPat (CharPat c _) = return $ S.VPX [Left c]

compileTm :: forall a. (NotRaw a, Show a, HasSource a) => Tm a -> Compile S.Exp
compileTm (SC sc _) = compileSComp sc
-- compileTm MkLet = return $ S.EV "let"
compileTm (StrTm s a) = compileDataCon (f s) where
  f :: String -> DataCon a
  f [] = DataCon "nil" [] a
  f (c:cs) = DataCon "cons" [CharTm c a, DCon (f cs) a] a
compileTm (IntTm n _) = return $ S.EI n
compileTm (CharTm c _) = return $ S.EX [Left c]
compileTm (TmSeq t1 t2 _) = (S.:!) <$> compileTm t1 <*> compileTm t2
compileTm (Use u _) = compileUse u
compileTm (DCon d _) = compileDataCon d

compileUse :: (NotRaw a, Show a, HasSource a) => Use a -> Compile S.Exp
compileUse (Op op _) = compileOp op
compileUse (App use xs _) = (S.:$) <$> compileUse use <*> mapM compileTm xs
compileUse (Lift p t _) = do e <- compileUse t
                             cmds <- msum <$> mapM getCCmds (S.toList p)
                             return $ S.ES cmds e

compileDataCon :: (NotRaw a, Show a, HasSource a) => DataCon a -> Compile S.Exp
compileDataCon (DataCon id xs _) = do xs' <- mapM compileTm xs
                                      return $ (S.EV id) S.:$ xs'

compileSComp :: (NotRaw a, Show a, HasSource a) => SComp a -> Compile S.Exp
compileSComp (SComp xs _) = S.EF <$> pure [[]] <*> mapM compileClause xs

compileOp :: Operator a -> Compile S.Exp
compileOp (Mono id _) = case M.lookup id builtins of
  Just v -> return $ S.EV v
  Nothing ->  do b <- isAtom id
                 return $ if b then S.EA id
                          else S.EV id
compileOp (Poly id _) = case M.lookup id builtins of
  Just v -> return $ S.EV v
  Nothing -> return $ S.EV id
compileOp (CmdId id _) = return $ S.EA id

builtins :: M.Map String String
builtins = M.fromList [("+", "plus")
                      ,("-", "minus")]

isBuiltin :: String -> Bool
isBuiltin x = M.member x builtins
