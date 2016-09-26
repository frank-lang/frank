module CompileTest where

import Parser
import Compile
import RefineSyntax
import qualified ExpectedTestOutput as ETO

compileProg progName =
  do p <- runTokenParse <$> readFile ("tests/" ++ progName ++ ".fk")
     case p of
       Left err -> print err
       Right prog -> case refine prog of
                       Left err -> print err
                       Right p' -> compile p' progName

main :: IO ()
main = compileProg "paper"
