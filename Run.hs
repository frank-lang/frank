module Run where

import Shonky.Semantics

runProg :: String -> IO ()
runProg pName = do env <- loadFile pName
                   print $ try env "main()"

main :: IO ()
main = runProg "listMap"
