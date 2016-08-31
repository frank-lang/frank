{-# LANGUAGE DataKinds #-}
module ExpectedTestOutput where

import Syntax

expected :: [IO (Prog Raw)]
expected = [
  -- tests/evalState.fk
  return $
  MkProg
  [MkItfTm (MkItf "State" ["X"]
            [MkCmd "get" (MkCType [] (MkPeg MkOpenAb
                                      (MkDTTy "X" MkEmpAb [])))
            ,MkCmd "put" (MkCType [MkPort MkIdAdj
                                   (MkDTTy "X" MkEmpAb [])]
                          (MkPeg MkOpenAb
                           (MkDTTy "Unit" MkEmpAb [])))])
  ,MkSigTm (MkSig "evalState"
            (MkCType [ MkPort MkIdAdj (MkDTTy "X" MkEmpAb [])
                     , MkPort (MkAdjPlus MkIdAdj "State"
                               [MkDTTy "X" MkEmpAb []])
                       (MkDTTy "Y" MkEmpAb [])]
             (MkPeg MkOpenAb (MkDTTy "Y" MkEmpAb []))))
  ,MkClsTm (MkMHCls "evalState"
            (MkCls [MkVPat (MkVarPat "x")
                   ,MkCmdPat "put" [MkVarPat "x'"] "k"]
             (MkRawComb "evalState" [MkRawId "x'"
                                    ,MkRawComb "k" [MkRawId "Unit"]])))
  ,MkClsTm (MkMHCls "evalState"
            (MkCls [MkVPat (MkVarPat "x")
                   ,MkCmdPat "get" [] "k"]
             (MkRawComb "evalState" [MkRawId "x"
                                    ,MkRawComb "k" [MkRawId "x"]])))
  ,MkClsTm (MkMHCls "evalState" (MkCls [MkVPat (MkVarPat "x")
                                       ,MkVPat (MkVarPat "y")]
                                 (MkRawId "y")))
  ,MkSigTm (MkSig "main" (MkCType [] (MkPeg MkOpenAb MkStringTy)))
  ,MkClsTm (MkMHCls "main"
            (MkCls []
             (MkRawComb "evalState"
              [MkStr "Hello"
              ,MkTmSeq (MkRawComb "put"
                        [MkRawComb "strcat"
                         [MkRawComb "get" []
                         ,MkStr " World!\n"]])
               (MkRawComb "get" [])])))]
  ]
