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
  -- tests/listMap.fk
  ,return $
   MkProg
   [MkDataTm (MkDT "List" ["X"]
              [MkCtr "Nil" [MkTVar "X"]
              ,MkCtr "Cons" [MkTVar "X"
                            ,MkDTTy "List" MkEmpAb [MkTVar "X"]
                            ,MkDTTy "List" MkEmpAb [MkTVar "X"]]])
   ,MkSigTm (MkSig "map"
             (MkCType
              [MkPort MkIdAdj
               (MkSCTy (MkCType [MkPort MkIdAdj
                                 (MkDTTy "a" MkEmpAb [])]
                        (MkPeg MkOpenAb (MkDTTy "b" MkEmpAb []))))
              ,MkPort MkIdAdj (MkDTTy "List" MkEmpAb [MkTVar "a"])]
              (MkPeg MkOpenAb (MkDTTy "List" MkEmpAb [MkTVar "b"]))))
  ,MkClsTm (MkMHCls "map" (MkCls [MkVPat (MkVarPat "f")
                                 ,MkVPat (MkVarPat "Nil")] (MkRawId "Nil")))
  ,MkClsTm (MkMHCls "map" (MkCls [MkVPat (MkVarPat "f")
                                 ,MkVPat (MkDataPat "Cons" [MkVarPat "x"
                                                           ,MkVarPat "xs"])]
                           (MkRawComb "Cons"
                            [MkRawComb "f" [MkRawId "x"]
                            ,MkRawComb "map" [MkRawId "f",MkRawId "xs"]])))
  ,MkSigTm (MkSig "main" (MkCType [] (MkPeg MkOpenAb
                                      (MkDTTy "List" MkEmpAb [MkIntTy]))))
  ,MkClsTm (MkMHCls "main"
            (MkCls [] (MkRawComb "map"
                       [MkSC (MkSComp [MkCls [MkVPat (MkVarPat "xs")]
                                       (MkRawId "xs")])
                       ,MkRawComb "Cons"
                        [MkInt 1
                        ,MkRawComb "Cons"
                         [MkInt 2
                         ,MkRawComb "Cons" [MkInt 3
                                           ,MkRawId "Nil"]]]])))]
   -- tests/suspended_computations.fk
  ,return $
   MkProg [MkDataTm (MkDT "Three" [] [MkCtr "Once" []
                                     ,MkCtr "Twice" []
                                     ,MkCtr "Thrice" []])
          ,MkSigTm (MkSig "id"
                    (MkCType [MkPort MkIdAdj (MkDTTy "a" MkEmpAb [])]
                     (MkPeg MkOpenAb (MkDTTy "a" MkEmpAb []))))
          ,MkClsTm (MkMHCls "id"
                    (MkCls [MkVPat (MkVarPat "x")] (MkRawId "x")))
          ,MkSigTm (MkSig "foo"
                    (MkCType [MkPort MkIdAdj (MkDTTy "Three" MkEmpAb [])]
                     (MkPeg MkOpenAb
                      (MkSCTy (MkCType
                               [MkPort MkIdAdj (MkDTTy "Three" MkEmpAb [])]
                               (MkPeg MkOpenAb MkIntTy))))))
          ,MkClsTm (MkMHCls "foo"
                    (MkCls [MkVPat (MkVarPat "Once")]
                     (MkRawComb "id"
                      [MkSC (MkSComp
                             [MkCls [MkVPat (MkVarPat "x")] (MkInt 1)])])))
          ,MkClsTm (MkMHCls "foo"
                    (MkCls [MkVPat (MkVarPat "Twice")]
                     (MkRawComb "id"
                      [MkSC (MkSComp
                             [MkCls [MkVPat (MkVarPat "Once")] (MkInt 1)
                             ,MkCls [MkVPat (MkVarPat "x")] (MkInt 1)])])))
          ,MkClsTm (MkMHCls "foo"
                    (MkCls [MkVPat (MkVarPat "Thrice")]
                     (MkRawComb "id"
                      [MkSC (MkSComp
                             [MkCls [MkVPat (MkVarPat "Once")] (MkInt 1)
                             ,MkCls [MkVPat (MkVarPat "Twice")] (MkInt 1)
                             ,MkCls [MkVPat (MkVarPat "x")] (MkInt 2)])])))]
   -- tests/fib.fk
  , return $ MkProg [MkSigTm (MkSig "fib"
                              (MkCType [MkPort MkIdAdj MkIntTy]
                               (MkPeg MkOpenAb MkIntTy)))
                    ,MkClsTm (MkMHCls "fib"
                              (MkCls [MkVPat (MkIntPat 0)] (MkInt 0)))
                    ,MkClsTm (MkMHCls "fib"
                              (MkCls [MkVPat (MkIntPat 1)] (MkInt 1)))
                    ,MkClsTm (MkMHCls "fib"
                              (MkCls [MkVPat (MkIntPat 2)] (MkInt 1)))
                    ,MkClsTm
                     (MkMHCls "fib"
                      (MkCls [MkVPat (MkVarPat "n")]
                       (MkRawComb "+"
                        [ MkRawComb "fib" [MkRawComb "-" [MkRawId "n"
                                                         ,MkInt 1]]
                        , MkRawComb "fib" [MkRawComb "-" [MkRawId "n"
                                                         ,MkInt 2]]])))
                    ,MkSigTm (MkSig "minusTwoOnZero"
                              (MkCType [MkPort MkIdAdj MkIntTy]
                               (MkPeg MkOpenAb MkIntTy)))
                    ,MkClsTm
                     (MkMHCls "minusTwoOnZero"
                      (MkCls [MkVPat (MkIntPat 0)]
                       (MkRawComb "-" [MkInt 0,MkInt 2])))
                    ,MkClsTm
                     (MkMHCls "minusTwoOnZero"
                      (MkCls [MkVPat (MkVarPat "n")] (MkInt 0)))
                    ,MkSigTm (MkSig "main"
                              (MkCType [] (MkPeg MkOpenAb MkIntTy)))
                    ,MkClsTm (MkMHCls "main"
                              (MkCls [] (MkRawComb "fib" [MkInt 5])))
                    ]
  , return $ MkProg []
  ]
