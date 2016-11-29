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

compileAndRunProg progName b =
  do p <- runTokenParse <$> readFile (progName ++ ".fk")
     case p of
       Left err -> die err
       Right prog -> case refine prog of
         Left err -> die err
         Right p' -> case check (desugar p') of
          Left err -> die err
          Right p' -> do env <- if b then
                                  do compileToFile p' progName
                                     loadFile progName
                                else
                                  -- Currently not producing runnable
                                  -- code.
                                  return $ load $ compile p'
                         case try env "main()" of
                           Ret v -> putStrLn $ ppVal v
                           comp -> putStrLn (show comp)

run x = compileAndRunProg x True --False

main :: IO ()
main = do
  args <- getArgs
  case args of
    [file] -> run file
    _      -> run "tests/paper"
