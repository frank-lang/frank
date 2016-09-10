-- Compile Frank to Shonky
module Compile where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax
import RefineSyntax
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

compile :: Prog Refined -> String -> IO ()
compile (MkProg xs) dst = do print res
                             writeFile (dst ++ ".uf") (S.ppProg res)
  where res = evalState (compile' xs) st
        st = initialiseItfMap initCState (getItfs xs)

compile' :: [TopTm Refined] -> Compile [S.Def S.Exp]
compile' xs = do liftM concat $ mapM compileTopTm xs

initialiseItfMap :: CState -> [Itf Refined] -> CState
initialiseItfMap st xs = st { imap = foldl f (imap st) xs }
  where f m (MkItf id _ xs) = foldl (ins id) m xs
        ins itf m (MkCmd cmd _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTm :: TopTm Refined -> Compile [S.Def S.Exp]
compileTopTm (MkDataTm x) = compileDatatype x
compileTopTm (MkDefTm x) = do def <- compileMHDef x
                              return $ [def]
compileTopTm _ = return [] -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: DataT Refined -> Compile [S.Def S.Exp]
compileDatatype (MkDT _ _ xs) = do xs <- nonNullary xs
                                   mapM compileCtr xs

nonNullary :: [Ctr Refined] -> Compile [Ctr Refined]
nonNullary ((MkCtr id []) : xs) = do addAtom id
                                     nonNullary xs
nonNullary (x : xs) = do xs' <- nonNullary xs
                         return $ x : xs'

compileCtr :: Ctr Refined -> Compile (S.Def S.Exp)
compileCtr (MkCtr id ts) = do let xs = take (length ts) $ repeat "x"
                                  xs' = zipWith f xs [1..]
                                  args = map (S.PV . S.VPV) xs'
                                  e = if (length xs') >= 2 then
                                        foldl1 (S.:&) $ map S.EV xs'
                                      else
                                        S.EV $ head xs'
                                  f x n = x ++ (show n)
                              return $ S.DF id [] [(args, e)]

-- use the type to generate the signature of commands handled
-- generate a clause 1-to-1 correspondence
compileMHDef :: MHDef Refined -> Compile (S.Def S.Exp)
compileMHDef (MkDef id ty xs) = do xs' <- mapM compileClause xs
                                   tyRep <- compileCType ty
                                   return $ S.DF id tyRep xs'

compileCType :: CType Refined -> Compile [[String]]
compileCType (MkCType xs _) = mapM compilePort xs

compilePort :: Port Refined -> Compile [String]
compilePort (MkPort adj _) = compileAdj adj

compileAdj :: Adj Refined -> Compile [String]
compileAdj MkIdAdj = return []
compileAdj (MkAdjPlus MkIdAdj id _) = do cmds <- getCCmds id
                                         return cmds
compileAdj (MkAdjPlus adj id _) = do xs <- compileAdj adj
                                     return $ xs ++ [id]

compileClause :: Clause Refined -> Compile ([S.Pat], S.Exp)
compileClause (MkCls ps tm) = do ps' <- mapM compilePattern ps
                                 e <- compileTm tm
                                 return (ps', e)

compilePattern :: Pattern -> Compile S.Pat
compilePattern (MkVPat x) = S.PV <$> compileVPat x
compilePattern (MkCmdPat cmd xs k) = do xs' <- mapM compileVPat xs
                                        return $ S.PC cmd xs' k
compilePattern (MkThkPat id) = return $ S.PT id

compileVPat :: ValuePat -> Compile S.VPat
compileVPat (MkVarPat id) = return $ S.VPV id
compileVPat (MkDataPat id xs) = return $ S.VPA id


compileTm :: Tm Refined -> Compile S.Exp
compileTm (MkSC sc) = return $ S.EV "sc"
compileTm MkLet = return $ S.EV "let"
compileTm (MkStr s) = return $ S.EX $ map Left s
compileTm (MkInt n) = return $ S.EI n
compileTm (MkTmSeq t1 t2) = (S.:!) <$> compileTm t1 <*> compileTm t2
compileTm (MkUse u) = compileUse u
compileTm (MkDCon d) = compileDataCon d

compileUse :: Use Refined -> Compile S.Exp
compileUse (MkOp op) = compileOp op
compileUse (MkApp op xs) = (S.:$) <$> compileOp op <*> mapM compileTm xs

compileDataCon :: DataCon Refined -> Compile S.Exp
compileDataCon (MkDataCon id []) = return $ S.EA id
compileDataCon (MkDataCon id xs) = do xs' <- mapM compileTm xs
                                      return $ (S.EV id) S.:$ xs'

compileOp :: Operator -> Compile S.Exp
compileOp (MkMono id) = do b <- isAtom id
                           return $ if b then S.EA id
                                    else S.EV id
compileOp (MkPoly id) = return $ S.EV id
compileOp (MkCmdId id) = return $ S.EA id

-- use the mappings of interface names to obtain the commands
