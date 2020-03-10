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
import Shonky.Renaming

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

compileToFile :: Prog Desugared -> String -> IO ()
compileToFile p dst = writeFile (dst ++ ".uf") (show $ ppProgShonky $ compile p)

compile :: Prog Desugared -> [S.Def S.Exp]
compile (MkProg xs) = res
  where res = reverse $ evalState (compile' xs) st
        st = initialiseItfMap initCState [i | ItfTm i _ <- xs]

compile' :: [TopTm Desugared] -> Compile [S.Def S.Exp]
compile' xs = do liftM concat $ mapM compileTopTm xs

initialiseItfMap :: CState -> [Itf Desugared] -> CState
initialiseItfMap st xs = st { imap = foldl f (imap st) xs }
  where f m (Itf id _ xs _) = foldl (ins id) m xs
        ins itf m (Cmd cmd _ _ _ _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTm :: TopTm Desugared -> Compile [S.Def S.Exp]
compileTopTm (DataTm x _) = compileDatatype x
compileTopTm (DefTm x@(Def id _ _ _) _) =
  if isBuiltin id then return []  else do def <- compileMHDef x
                                          return $ [def]
compileTopTm _ = return [] -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: DataT Desugared -> Compile [S.Def S.Exp]
compileDatatype (DT _ _ xs _) = mapM compileCtr xs

-- nonNullary :: [Ctr a] -> Compile [Ctr a]
-- nonNullary ((MkCtr id []) : xs) = do addAtom id
--                                      nonNullary xs
-- nonNullary (x : xs) = do xs' <- nonNullary xs
--                          return $ x : xs'
-- nonNullary [] = return []

compileCtr :: Ctr Desugared -> Compile (S.Def S.Exp)
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
compileMHDef :: MHDef Desugared -> Compile (S.Def S.Exp)
compileMHDef (Def id ty xs _) = do xs' <- mapM compileClause xs
                                   tyRep <- compileCType ty
                                   return $ S.DF id tyRep xs'

compileCType :: CType Desugared -> Compile [([S.Adap], [String])]
compileCType (CType xs _ _) = mapM compilePort xs

compilePort :: Port Desugared -> Compile ([S.Adap], [String])
compilePort p@(Port adjs _ _) =
  do let (insts, adps) = adjsNormalForm adjs
     -- convert insts into list of commands
     let insts' = M.mapWithKey (\i insts ->
                                replicate ((length . bwd2fwd) insts) i) insts
     cmds <- liftM concat $ mapM getCCmds (concat (M.elems insts'))
     -- convert renamings into list of Adap
     let (ids, rens) = unzip (M.assocs adps)   -- (id, ren)
     rencmds <- mapM getCCmds ids
     return (zip rencmds rens, cmds)

compileClause :: Clause Desugared -> Compile ([S.Pat], S.Exp)
compileClause (Cls ps tm _) = do ps' <- mapM compilePattern ps
                                 e <- compileTm tm
                                 return (ps', e)

compilePattern :: Pattern Desugared -> Compile S.Pat
compilePattern (VPat x _) = S.PV <$> compileVPat x
compilePattern c@(CmdPat cmd n xs k _) = do xs' <- mapM compileVPat xs
                                            return $ S.PC cmd n xs' k
compilePattern (ThkPat id _) = return $ S.PT id

-- The current version simply represents Frank characters as one
-- character Shonky strings and Frank strings as a Shonky datatype
-- with "cons" and "nil" constructors.

compileVPat :: ValuePat Desugared -> Compile S.VPat
compileVPat (VarPat id _) = return $ S.VPV id
compileVPat (DataPat id xs _) =
  do case xs of
       []  -> return $ S.VPA id S.:&: S.VPA ""
       xs -> do xs' <- mapM compileVPat xs
                return $ foldr1 (S.:&:) $ (S.VPA id) : (xs' ++ [S.VPA ""])
compileVPat (IntPat n _) = return $ S.VPI n
compileVPat ((StrPat s a) :: ValuePat Desugared) = compileVPat (compileStrPat s) where
  compileStrPat :: String -> ValuePat Desugared
  compileStrPat []     = DataPat "nil" [] a
  compileStrPat (c:cs) = DataPat "cons" [CharPat c a, compileStrPat cs] a
compileVPat (CharPat c _) = return $ S.VPX [Left c]
compileVPat (FloatPat f _) = return $ S.VPD f

compileTm :: Tm Desugared -> Compile S.Exp
compileTm (SC sc _) = compileSComp sc
-- compileTm MkLet = return $ S.EV "let"
compileTm (StrTm s a) = compileDataCon (f s) where
  f :: String -> DataCon Desugared
  f [] = DataCon "nil" [] a
  f (c:cs) = DataCon "cons" [CharTm c a, DCon (f cs) a] a
compileTm (IntTm n _) = return $ S.EI n
compileTm (FloatTm f _) = return $ S.ED f
compileTm (CharTm c _) = return $ S.EX [Left c]
compileTm (TmSeq t1 t2 _) = (S.:!) <$> compileTm t1 <*> compileTm t2
compileTm (Use u _) = compileUse u
compileTm (DCon d _) = compileDataCon d

compileUse :: Use Desugared -> Compile S.Exp
compileUse (Op op _) = compileOp op
compileUse (App use xs _) = (S.:$) <$> compileUse use <*> mapM compileTm xs
compileUse (Adapted [] t _) = compileUse t
compileUse (Adapted (r:rr) t a) =
  do (cs, r') <- compileAdaptor r
     rest <- compileUse (Adapted rr t a)
     return $ S.ER (cs, r') rest

compileAdaptor :: Adaptor Desugared -> Compile ([String], Renaming)
compileAdaptor adp@(CompilableAdp x m ns _) = do
  cmds <- getCCmds x
  return (cmds, adpToRen adp)


compileDataCon :: DataCon Desugared -> Compile S.Exp
compileDataCon (DataCon id xs _) = do xs' <- mapM compileTm xs
                                      return $ (S.EV id) S.:$ xs'

compileSComp :: SComp Desugared -> Compile S.Exp
compileSComp (SComp xs _) = S.EF <$> pure [([], [])] <*> mapM compileClause xs
-- TODO: LC: Fix this!

compileOp :: Operator Desugared -> Compile S.Exp
compileOp (VarId id _) = case M.lookup id builtins of
  Just v -> return $ S.EV v
  Nothing ->  do b <- isAtom id
                 return $ if b then S.EA id
                          else S.EV id
compileOp (CmdId id _) = return $ S.EA id

builtins :: M.Map String String
builtins = M.fromList [("+", "plus")
                      ,("-", "minus")
                      ,("+~", "plusF")
                      ,("-~", "minusF")
                      ,("*~", "multF")
                      ,("/~", "divF")
                      ,("eqc" , "eqc")
                      ,(">", "gt")
                      ,("<", "lt")]

isBuiltin :: String -> Bool
isBuiltin x = M.member x builtins
