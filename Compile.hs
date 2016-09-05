-- Compile Frank to Shonky
module Compile where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.Map.Strict as M

import Syntax
import RefineSyntax

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
compile (MkProg xs) dst = writeFile (dst ++ ".uf") res
  where res = evalState (compile' xs) st
        st = initialiseItfMap initCState (getItfs xs)

compile' :: [TopTm Refined] -> Compile String
compile' xs = do xs' <- mapM compileTopTm xs
                 return $ unlines $ xs'

initialiseItfMap :: CState -> [Itf Refined] -> CState
initialiseItfMap st xs = st { imap = foldl f (imap st) xs }
  where f m (MkItf id _ xs) = foldl (ins id) m xs
        ins itf m (MkCmd cmd _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTm :: TopTm Refined -> Compile String
compileTopTm (MkDataTm x) = compileDatatype x
compileTopTm (MkDefTm x) = compileMHDef x
compileTopTm _ = return $ "" -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: DataT Refined -> Compile String
compileDatatype (MkDT _ _ xs) = liftM unlines $ mapM compileCtr xs

compileCtr :: Ctr Refined -> Compile String
compileCtr (MkCtr id xs) = return ""

-- use the type to generate the signature of commands handled
-- generate a clause 1-to-1 correspondence
compileMHDef :: MHDef Refined -> Compile String
compileMHDef (MkDef id ty xs) = do xs' <- mapM compileClause xs
                                   tyRep <- compileCType ty
                                   let header = id ++ "(" ++ tyRep ++ "):"
                                   return $ unlines $ [header] ++ xs'

compileCType :: CType Refined -> Compile String
compileCType (MkCType xs _) = liftM (intercalate ", ") $ mapM compilePort xs

compilePort :: Port Refined -> Compile String
compilePort (MkPort adj _) = compileAdj adj

compileAdj :: Adj Refined -> Compile String
compileAdj MkIdAdj = return ""
compileAdj (MkAdjPlus MkIdAdj id _) = liftM (intercalate " ") $ getCCmds id
compileAdj (MkAdjPlus adj id _) = do adj' <- compileAdj adj
                                     return $ adj' ++ " " ++ id

compileClause :: Clause Refined -> Compile String
compileClause (MkCls _ _) = return ""

-- use the mappings of interface names to constructors to obtain the commands
-- use the constructor mapping to generate atoms for constructors
