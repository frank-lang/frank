module Main where

import Parser
import TypeCheck
import RefineSyntax
import DesugarSyntax
import qualified ExpectedTestOutput as ETO

tcProg progName =
  do p <- runTokenParse <$> readFile ("tests/" ++ progName ++ ".fk")
     case p of
       Left err -> print err
       Right prog -> case refine prog of
         Left err -> print err
         Right p' -> print p'

main :: IO ()
main = tcProg "paper"
