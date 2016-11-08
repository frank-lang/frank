module Main where

import Parser
import Compile
import TypeCheck
import RefineSyntax
import DesugarSyntax
import qualified ExpectedTestOutput as ETO

import Shonky.Semantics

compileAndRunProg progName =
  do p <- runTokenParse <$> readFile ("tests/" ++ progName ++ ".fk")
     case p of
       Left err -> print err
       Right prog -> case refine prog of
         Left err -> print err
         Right p' -> case check (desugar p') of
          Left err -> print err
          Right p' -> do compile p' progName
                         env <- load progName
                         case try env "main()" of
                           Ret v -> print $ ppVal v
                           comp -> print comp

main :: IO ()
main = compileAndRunProg "paper"
