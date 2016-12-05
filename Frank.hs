module Main where

import Parser
import Compile
import TypeCheck
import RefineSyntax
import DesugarSyntax
import System.Environment
import qualified ExpectedTestOutput as ETO

import Shonky.Semantics

import System.Console.CmdArgs.Explicit
import System.Environment
import System.Exit
import System.IO

parseProg fileName _ = runTokenParse <$> readFile fileName

checkProg p _ =
  case p of
    Left err -> die err
    Right p -> case refine p of
      Left err -> die err
      Right p' -> case check (desugar p') of
        Left err -> die err
        Right p' -> return p'

compileProg progName p args =
  do env <- if ("output-shonky","") `elem` args then
              do compileToFile p progName
                 loadFile progName
            else return $ load $ compile p
     return env

evalProg env tm =
  case try env tm of
    Ret v -> putStrLn $ ppVal v
    comp -> do v <- ioHandler comp
               putStrLn $ ppVal v

compileAndRunProg fileName args =
  do let progName = takeWhile (\c -> c /= '.') fileName
     p <- parseProg fileName args
     p' <- checkProg p args
     env <- compileProg progName p' args
     case lookup "eval" args of
       Just v -> evalProg env v
       Nothing -> evalProg env "main()"

arguments :: Mode [(String,String)]
arguments =
  mode "frank" [] "Frank program" (flagArg (upd "file") "FILE")
  [flagNone ["output-shonky"] (("output-shonky",""):) "Output Shonky code"
  ,flagHelpSimple (("help",""):)]
  where upd msg x v = Right $ (msg,x):v

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  args <- processArgs arguments
  if ("help","") `elem` args then
     print $ helpText [] HelpFormatDefault arguments
  else case lookup "file" args of
    Just f -> compileAndRunProg f args
    Nothing -> die "no Frank source specified."
