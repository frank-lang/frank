module CompileTest where

import Parser
import Compile
import RefineSyntax
import qualified ExpectedTestOutput as ETO

main :: IO ()
main = do p <- runCharParse <$> readFile "tests/paper.fk"
          case p of
            Left err -> print err
            Right prog -> case refine prog of
                            Left err -> print err
                            Right p' -> compile p' "paper"
