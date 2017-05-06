{-# LANGUAGE GADTs #-}
module Main where

import Parser
import Compile
import TypeCheck
import Syntax
import RefineSyntax
import DesugarSyntax
import System.Environment

import Shonky.Semantics

import Data.IORef
import qualified Data.Map.Strict as M
import Data.List

import System.Console.CmdArgs.Explicit
import System.Environment
import System.Exit
import System.IO

type Args = [(String,String)]

splice :: Prog Raw -> Tm Raw -> Prog Raw
splice (MkProg xs) tm = MkProg $ xs ++ ys
  where ys = [sig, cls]
        sig = MkSigTm (MkSig id (MkCType [] peg))
        peg = MkPeg ab ty
        ty = MkTVar "%X"
        ab = MkAb (MkAbVar "£") M.empty
        cls = MkClsTm (MkMHCls id (MkCls [] tm))
        id = "%eval"

exorcise :: Prog Desugared -> (Prog Desugared, TopTm Desugared)
exorcise (MkProg xs) = (prog,MkDefTm (head evalDef))
  where prog = MkProg (map MkDataTm dts ++
                       map MkItfTm itfs ++
                       map MkDefTm hdrs)
        (dts,itfs,defs) = (getDataTs xs,getItfs xs,getDefs xs)
        (evalDef,hdrs) = partition isEvalTm defs
        isEvalTm (MkDef id _ _) = id == "%eval"

extractEvalUse :: TopTm Desugared -> Use Desugared
extractEvalUse (MkDefTm (MkDef _ _ [cls])) = getBody cls
  where getBody (MkCls [] (MkUse u)) = u
        getBody _ = error "extractEvalUse: eval body invariant broken"

glue :: Prog Desugared -> TopTm Desugared -> Prog Desugared
glue (MkProg xs) x = MkProg (x : xs)

parseProg fileName _ = runTokenProgParse <$> readFile fileName

parseEvalTm v = case runTokenParse parseRawTm v of
  Left err -> die err
  Right tm -> return tm

refineComb prog tm = case prog of
    Left err -> die err
    Right p -> case refine (splice p tm) of
      Left err -> die err
      Right p' -> return p'

refineAndDesugarProg :: Either String (Prog Raw) -> IO (Prog Desugared)
refineAndDesugarProg p =
  case p of
    Left err -> die err
    Right p -> case refine p of
      Left err -> die err
      Right p' -> return $ desugar p'

checkProg :: Prog Desugared -> Args -> IO (Prog Desugared)
checkProg p _ =
  case check p of
    Left err -> die err
    Right p' -> return p'

checkUse :: Prog Desugared -> Use Desugared -> IO (VType Desugared)
checkUse p use =
  case inferEvalUse p use of
    Left err -> die err
    Right ty -> return ty

compileProg progName p args =
  do env <- if ("output-shonky","") `elem` args then
              do compileToFile p progName
                 loadFile progName
            else return $ load $ compile p
     return env

evalProg env tm =
  case try env tm of
    Ret v -> putStrLn $ ppVal v
    comp -> do -- putStrLn $ "Generated computation: " ++ show comp
               v <- ioHandler comp
               putStrLn $ ppVal v

compileAndRunProg fileName args =
  do let progName = takeWhile (\c -> c /= '.') fileName
     prog <- parseProg fileName args
     case lookup "eval" args of
       Just v -> do tm <- parseEvalTm v
                    p <- refineComb prog tm
                    let (p',tm) = exorcise (desugar p)
                        use = extractEvalUse tm
                    _ <- checkProg p' args
                    _ <- checkUse p' use
                    env <- compileProg progName (glue p' tm) args
                    evalProg env "%eval()"
       Nothing -> do p <- refineAndDesugarProg prog
                     _ <- checkProg p args
                     env <- compileProg progName p args
                     case lookup "entry-point" args of
                       Just v ->  evalProg env (v ++ "()")
                       Nothing -> evalProg env "main()"

arguments :: Mode Args
arguments =
  mode "frank" [] "Frank program" (flagArg (upd "file") "FILE")
  [flagNone ["output-shonky"] (("output-shonky",""):) "Output Shonky code"
  ,flagNone ["debug-output"] (("debug-output",""):)
   "Enable output for debugging the Frank system"
  ,flagReq ["eval"] (upd "eval") "USE"
   "Run Frank computation USE (default: main!)"
  ,flagReq ["entry-point"] (upd "entry-point") "NAME"
   "Run computation NAME (default: main)"
  ,flagHelpSimple (("help",""):)]
  where upd msg x v = Right $ (msg,x):v

-- handy for testing in ghci
run f = compileAndRunProg f []

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  args <- processArgs arguments
  writeIORef debugMode (("debug-output","") `elem` args)
  if ("help","") `elem` args then
     print $ helpText [] HelpFormatDefault arguments
  else case lookup "file" args of
    Just f -> compileAndRunProg f args
    Nothing -> die "no Frank source specified."
