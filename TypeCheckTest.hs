module Main where

import Parser
import TypeCheck
import RefineSyntax
import DesugarSyntax

tcProg progName =
  do p <- runTokenProgParse <$> readFile (progName ++ ".fk")
     case p of
       Left err -> print err
       Right prog -> case refine prog of
         Left err -> print err
         Right p' -> case check (desugar p') of
           Left err -> print err
           Right p' -> print "typechecking succeeded!"

main :: IO ()
main = tcProg "paper"
