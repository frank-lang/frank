{-# LANGUAGE DataKinds #-}
module ExpectedTestOutput where

import qualified Data.Map.Strict as M

import Syntax

expected :: [IO (Prog Raw)]
expected = [
  -- tests/evalState.fk
  return $
  MkProg
  [MkItfTm (MkItf "State" ["X"]
            [MkCmd "get" [] (MkDTTy "X" [MkAb MkEmpAb M.empty] [])
            ,MkCmd "put" [MkDTTy "X" [MkAb MkEmpAb M.empty] []]
                          (MkDTTy "Unit" [MkAb MkEmpAb M.empty] [])])
  ,MkSigTm (MkSig "evalState"
            (MkCType [ MkPort (MkAdj M.empty) (MkDTTy "X" [MkAb MkEmpAb M.empty] [])
                     , MkPort (MkAdj (M.fromList [("State",[MkDTTy "X"[MkAb MkEmpAb M.empty] []])]))
                       (MkDTTy "Y" [MkAb MkEmpAb M.empty] [])]
             (MkPeg (MkAb (MkAbVar "£") M.empty) (MkDTTy "Y" [MkAb MkEmpAb M.empty] []))))
  ,MkClsTm (MkMHCls "evalState"
            (MkCls [MkVPat (MkVarPat "x")
                   ,MkCmdPat "put" [MkVarPat "x'"] "k"]
             (MkRawComb "evalState" [MkRawId "x'"
                                    ,MkRawComb "k" [MkRawId "unit"]])))
  ,MkClsTm (MkMHCls "evalState"
            (MkCls [MkVPat (MkVarPat "x")
                   ,MkCmdPat "get" [] "k"]
             (MkRawComb "evalState" [MkRawId "x"
                                    ,MkRawComb "k" [MkRawId "x"]])))
  ,MkClsTm (MkMHCls "evalState" (MkCls [MkVPat (MkVarPat "x")
                                       ,MkVPat (MkVarPat "y")]
                                 (MkRawId "y")))
  ,MkSigTm (MkSig "main" (MkCType [] (MkPeg (MkAb (MkAbVar "£") M.empty) MkStringTy)))
  -- FIXME
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
   [MkSigTm (MkSig "map"
             (MkCType
              [MkPort (MkAdj M.empty)
               (MkSCTy (MkCType [MkPort (MkAdj M.empty)
                                 (MkDTTy "a" [MkAb MkEmpAb M.empty] [])]
                        (MkPeg (MkAb (MkAbVar "£") M.empty) (MkDTTy "b" [MkAb MkEmpAb M.empty] []))))
              ,MkPort (MkAdj M.empty) (MkDTTy "List" [MkAb MkEmpAb M.empty] [MkTVar "a"])]
              (MkPeg (MkAb (MkAbVar "£") M.empty) (MkDTTy "List" [MkAb MkEmpAb M.empty] [MkTVar "b"]))))
  ,MkClsTm (MkMHCls "map" (MkCls [MkVPat (MkVarPat "f")
                                 ,MkVPat (MkVarPat "nil")] (MkRawId "nil")))
  ,MkClsTm (MkMHCls "map" (MkCls [MkVPat (MkVarPat "f")
                                 ,MkVPat (MkDataPat "cons" [MkVarPat "x"
                                                           ,MkVarPat "xs"])]
                           (MkRawComb "cons"
                            [MkRawComb "f" [MkRawId "x"]
                            ,MkRawComb "map" [MkRawId "f",MkRawId "xs"]])))
  ,MkSigTm (MkSig "main" (MkCType [] (MkPeg (MkAb (MkAbVar "£") M.empty)
                                      (MkDTTy "List" [MkAb MkEmpAb M.empty] [MkIntTy]))))
  ,MkClsTm (MkMHCls "main"
            (MkCls [] (MkRawComb "map"
                       [MkSC (MkSComp [MkCls [MkVPat (MkVarPat "xs")]
                                       (MkRawId "xs")])
                       ,MkRawComb "cons"
                        [MkInt 1
                        ,MkRawComb "cons"
                         [MkInt 2
                         ,MkRawComb "cons" [MkInt 3
                                           ,MkRawId "nil"]]]])))]
   -- tests/suspended_computations.fk
  ,return $
   MkProg [MkDataTm (MkDT "Three" [] [] [MkCtr "Once" []
                                        ,MkCtr "Twice" []
                                        ,MkCtr "Thrice" []])
          ,MkSigTm (MkSig "id"
                    (MkCType [MkPort (MkAdj M.empty) (MkDTTy "a" [MkAb MkEmpAb M.empty] [])]
                     (MkPeg (MkAb (MkAbVar "£") M.empty) (MkDTTy "a" [MkAb MkEmpAb M.empty] []))))
          ,MkClsTm (MkMHCls "id"
                    (MkCls [MkVPat (MkVarPat "x")] (MkRawId "x")))
          ,MkSigTm (MkSig "foo"
                    (MkCType [MkPort (MkAdj M.empty) (MkDTTy "Three" [MkAb MkEmpAb M.empty] [])]
                     (MkPeg (MkAb (MkAbVar "£") M.empty)
                      (MkSCTy (MkCType
                               [MkPort (MkAdj M.empty) (MkDTTy "Three" [MkAb MkEmpAb M.empty] [])]
                               (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy))))))
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
                              (MkCType [MkPort (MkAdj M.empty) MkIntTy]
                               (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)))
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
                              (MkCType [MkPort (MkAdj M.empty) MkIntTy]
                               (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)))
                    ,MkClsTm
                     (MkMHCls "minusTwoOnZero"
                      (MkCls [MkVPat (MkIntPat 0)]
                       (MkRawComb "-" [MkInt 0,MkInt 2])))
                    ,MkClsTm
                     (MkMHCls "minusTwoOnZero"
                      (MkCls [MkVPat (MkVarPat "n")] (MkInt 0)))
                    ,MkSigTm (MkSig "main"
                              (MkCType [] (MkPeg (MkAb (MkAbVar "£") M.empty) MkIntTy)))
                    ,MkClsTm (MkMHCls "main"
                              (MkCls [] (MkRawComb "fib" [MkInt 5])))
                    ]
  , return $ MkProg []
  ]
