-- Compile Frank to Shonky
module Compile where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.Map.Strict as M

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

data CState = MkCState { imap :: ItfCmdMap }

initCState :: CState
initCState = MkCState M.empty

getCState :: Compile CState
getCState = get

setCState :: CState -> Compile ()
setCState = put

getCCmds :: Id -> Compile [Id]
getCCmds itf = do s <- getCState
                  return $ M.findWithDefault [] itf (imap s)

compile :: Prog Refined -> String -> IO ()
compile (MkProg xs) dst = do print (show res)
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
compileDatatype (MkDT _ _ xs) = mapM compileCtr xs

compileCtr :: Ctr Refined -> Compile (S.Def S.Exp)
compileCtr (MkCtr id xs) = return $ id S.:= S.EV ""

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
compileTm tm = return $ S.EV "tm"

-- use the mappings of interface names to constructors to obtain the commands
-- use the constructor mapping to generate atoms for constructors
