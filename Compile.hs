{-# LANGUAGE ScopedTypeVariables #-}

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

compileToFile :: NotRaw a => Prog a -> String -> IO ()
compileToFile p dst = writeFile (dst ++ ".uf") (S.ppProg $ compile p)

compile :: NotRaw a => Prog a -> [S.Def S.Exp]
compile (MkProg xs) = res
  where res = reverse $ evalState (compile' xs) st
        st = initialiseItfMap initCState (getItfs xs)

compile' :: NotRaw a => [TopTm a] -> Compile [S.Def S.Exp]
compile' xs = do liftM concat $ mapM compileTopTm xs

initialiseItfMap :: NotRaw a => CState -> [Itf a] -> CState
initialiseItfMap st xs = st { imap = foldl f (imap st) xs }
  where f m (MkItf id _ xs) = foldl (ins id) m xs
        ins itf m (MkCmd cmd _ _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTm :: NotRaw a => TopTm a -> Compile [S.Def S.Exp]
compileTopTm (MkDataTm x) = compileDatatype x
compileTopTm (MkDefTm x@(MkDef id _ _)) = if isBuiltin id then return []
                                          else do def <- compileMHDef x
                                                  return $ [def]
compileTopTm _ = return [] -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: NotRaw a => DataT a -> Compile [S.Def S.Exp]
compileDatatype (MkDT _ _ xs) = mapM compileCtr xs

-- nonNullary :: [Ctr a] -> Compile [Ctr a]
-- nonNullary ((MkCtr id []) : xs) = do addAtom id
--                                      nonNullary xs
-- nonNullary (x : xs) = do xs' <- nonNullary xs
--                          return $ x : xs'
-- nonNullary [] = return []

compileCtr :: NotRaw a => Ctr a -> Compile (S.Def S.Exp)
compileCtr (MkCtr id []) = return $ S.DF id [] [([], S.EA id S.:& S.EA "")]
compileCtr (MkCtr id ts) =
  let f x n = x ++ (show n) in
  let xs = take (length ts) $ repeat "x" in
  let xs' = zipWith f xs [1..] in
  let args = map (S.PV . S.VPV) xs' in
  let e = foldr1 (S.:&) $ (S.EA id) : (map S.EV xs' ++ [S.EA ""]) in
  return $ S.DF id [] [(args, e)]

-- use the type to generate the signature of commands handled
-- generate a clause 1-to-1 correspondence
compileMHDef :: NotRaw a => MHDef a -> Compile (S.Def S.Exp)
compileMHDef (MkDef id ty xs) = do xs' <- mapM compileClause xs
                                   tyRep <- compileCType ty
                                   return $ S.DF id tyRep xs'

compileCType :: NotRaw a => CType a -> Compile [[String]]
compileCType (MkCType xs _) = mapM compilePort xs

compilePort :: NotRaw a => Port a -> Compile [String]
compilePort (MkPort adj _) = compileAdj adj

compileAdj :: NotRaw a => Adj a -> Compile [String]
compileAdj (MkAdj m) = do cmds <- liftM concat $ mapM getCCmds (M.keys m)
                          return cmds

compileClause :: NotRaw a => Clause a -> Compile ([S.Pat], S.Exp)
compileClause (MkCls ps tm) = do ps' <- mapM compilePattern ps
                                 e <- compileTm tm
                                 return (ps', e)

compilePattern :: NotRaw a => Pattern a -> Compile S.Pat
compilePattern (MkVPat x) = S.PV <$> compileVPat x
compilePattern (MkCmdPat cmd xs k) = do xs' <- mapM compileVPat xs
                                        return $ S.PC cmd xs' k
compilePattern (MkThkPat id) = return $ S.PT id

-- The current version simply represents Frank characters as one
-- character Shonky strings and Frank strings as a Shonky datatype
-- with "cons" and "nil" constructors.

compileVPat :: NotRaw a => ValuePat a -> Compile S.VPat
compileVPat (MkVarPat id) = return $ S.VPV id
compileVPat (MkDataPat id xs) =
  do case xs of
       []  -> return $ S.VPA id S.:&: S.VPA ""
       xs -> do xs' <- mapM compileVPat xs
                return $ foldr1 (S.:&:) $ (S.VPA id) : (xs' ++ [S.VPA ""])
compileVPat (MkIntPat n) = return $ S.VPI n
compileVPat ((MkStrPat s) :: ValuePat a) = compileVPat (compileStrPat s) where
  compileStrPat :: NotRaw a => String -> ValuePat a
  compileStrPat []     = MkDataPat "nil" []
  compileStrPat (c:cs) = MkDataPat "cons" [MkCharPat c, compileStrPat cs]
compileVPat (MkCharPat c) = return $ S.VPX [Left c]

compileTm :: NotRaw a => Tm a -> Compile S.Exp
compileTm (MkSC sc) = compileSComp sc
-- compileTm MkLet = return $ S.EV "let"
compileTm (MkStr s :: Tm a) = compileDataCon (f s) where
  f :: String -> DataCon a
  f [] = MkDataCon "nil" []
  f (c:cs) = MkDataCon "cons" [MkChar c, MkDCon $ f cs]
compileTm (MkInt n) = return $ S.EI n
compileTm (MkChar c) = return $ S.EX [Left c]
compileTm (MkTmSeq t1 t2) = (S.:!) <$> compileTm t1 <*> compileTm t2
compileTm (MkUse u) = compileUse u
compileTm (MkDCon d) = compileDataCon d

compileUse :: NotRaw a => Use a -> Compile S.Exp
compileUse (MkOp op) = compileOp op
compileUse (MkApp use xs) = (S.:$) <$> compileUse use <*> mapM compileTm xs

compileDataCon :: NotRaw a => DataCon a -> Compile S.Exp
compileDataCon (MkDataCon id xs) = do xs' <- mapM compileTm xs
                                      return $ (S.EV id) S.:$ xs'

compileSComp :: NotRaw a => SComp a -> Compile S.Exp
compileSComp (MkSComp xs) = S.EF <$> pure [[]] <*> mapM compileClause xs

compileOp :: Operator -> Compile S.Exp
compileOp (MkMono id) = case M.lookup id builtins of
  Just v -> return $ S.EV v
  Nothing ->  do b <- isAtom id
                 return $ if b then S.EA id
                          else S.EV id
compileOp (MkPoly id) = case M.lookup id builtins of
  Just v -> return $ S.EV v
  Nothing -> return $ S.EV id
compileOp (MkCmdId id) = return $ S.EA id

builtins :: M.Map String String
builtins = M.fromList [("+", "plus")
                      ,("-", "minus")]

isBuiltin :: String -> Bool
isBuiltin x = M.member x builtins
