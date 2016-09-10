module CompileTest where

import Compile
import RefineSyntax
import qualified ExpectedTestOutput as ETO

main :: IO ()
main = do p <- head ETO.expected -- evalState.fk
          case refine p of
            Left err -> print err
            Right p' -> compile p' "evalState"
