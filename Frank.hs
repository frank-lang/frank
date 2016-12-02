module Main where

import Parser
import Compile
import TypeCheck
import RefineSyntax
import DesugarSyntax
import System.Environment
import qualified ExpectedTestOutput as ETO

import Shonky.Semantics

import System.Environment
import System.Exit

parseAndCheckProg progName b =
  do p <- runTokenParse <$> readFile progName
     case p of
       Left err -> die err
       Right prog -> case refine prog of
         Left err -> die err
         Right p' -> case check (desugar p') of
          Left err -> die err
          Right p' -> do env <- if b then
                                  do compileToFile p' progName
                                     loadFile progName
                                else return $ load $ compile p'
                         return env

compileAndRunProg progName b =
  do env <- parseAndCheckProg progName b
     case try env "main()" of
       Ret v -> putStrLn $ ppVal v
       comp -> putStrLn (show comp)

run x = compileAndRunProg x False

runWithOpts x opts =
  case opts of
    "--output-shonky" : opts -> compileAndRunProg x True
    _ -> run x

main :: IO ()
main = do
  args <- getArgs
  case args of
    file : opts -> runWithOpts file opts
    _      -> run "tests/paper.fk"
