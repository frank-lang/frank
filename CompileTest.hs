module CompileTest where

import Parser
import Compile
import RefineSyntax

compileProg progName =
  do p <- runTokenProgParse <$> readFile (progName ++ ".fk")
     case p of
       Left err -> print err
       Right prog -> case refine prog of
                       Left err -> print err
                       Right p' -> compileToFile p' progName

main :: IO ()
main = compileProg "paper"
