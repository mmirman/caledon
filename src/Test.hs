module Src.Test where

import Src.HOU
import Src.AST

tt = tipe ~> tipe
ttt = tipe ~> tt
tttt = tipe ~> ttt

test3 :: Form
test3 = Bind tipe -- 2
      $ Bind tipe -- 1 
      $ Bind tipe -- 0 
      $ Pat (evvar 0 "a" tttt :+: var 1 :+: var 0 :+: var 2) :=: Pat (evvar 0 "a" tttt :+: var 2 :+: var 0 :+: var 1)
     :&: evar 1 "n" tttt :=: evar 0 "a" tttt -- to view the result!

test2 :: Form
test2 = Bind ttt  -- 3
      $ Bind tt   -- 2
      $ Bind tipe -- 1
      $ Bind tipe -- 0 
      $ Pat (evvar 2 "a" ttt :+: var 1 :+: var 0) :=: Pat (vvar 2 :+: var 0)
     :&: evar 3 "g" ttt :=: evar 2 "a" ttt -- to view the result!

test1 :: Form
test1 = Bind tt   -- 2
      $ Bind tipe -- 1
      $ Bind tipe -- 0 
      $ Pat (evvar 2 "a" ttt :+: var 1 :+: var 0) :=: var 1
     :&: evar 3 "z" ttt :=: evar 2 "a" ttt -- to view the result!

testN :: Form
testN = Bind tipe
      $ Bind tipe
      $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 1 "x" tt :+: var 0)
      
testN1 :: Form
testN1 = Bind tipe
       $ Bind tipe
       $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" ttt :+: var 1 :+: var 0)      
      :&: evar 0 "x@" ttt :=: evar 0 "x@" ttt
       
testN1p :: Form
testN1p = Bind tipe
        $ Bind tipe
        $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" tt :+: var 0)      
       :&: evar 0 "z" ttt :=: evar 1 "arg" ttt
       :&: evar 1 "zola" tt :=: evar 0 "x@" tt
