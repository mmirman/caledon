module Src.Test where

import Src.Substitution
import Control.Monad.State
import Control.Monad.Error
import Data.Monoid

import Src.HOU
import Src.AST

t = tipemake "uni"
tt = t ~> t
ttt = t ~> tt
tt_t = tt ~> t
tt_tt = tt ~> tt
tttt = t ~> ttt

test3 :: Form
test3 = Bind t -- 2
      $ Bind t -- 1 
      $ Bind t -- 0 
      $ Pat (evvar 0 "a" tttt :+: var 1 :+: var 0 :+: var 2) :=: Pat (evvar 0 "a" tttt :+: var 2 :+: var 0 :+: var 1)

test2 :: Form  
test2 = Bind tt   -- 2
      $ Bind t -- 1
      $ Bind t -- 0 
      $ Pat (evvar 1 "x" ttt :+: var 1 :+: var 0) :=: Pat (vvar 2 :+: var 0)

test1 :: Form
test1 = Bind t -- 1
      $ Bind t -- 0 
      $ Pat (evvar 0 "x" ttt :+: var 1 :+: var 0) :=: var 1




testN :: Form
testN = Bind t
      $ Bind t
      $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 1 "x" tt :+: var 0)
      
testN1 :: Form
testN1 = Bind t
       $ Bind t
       $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" ttt :+: var 1 :+: var 0)      
      :&: evar 0 "x@" ttt :=: evar 0 "x@" ttt
       
testN1p :: Form
testN1p = Bind t
        $ Bind t
        $ Pat (evvar 0 "z" ttt :+: var 1 :+: var 0) :=: Pat (evvar 0 "x@" tt :+: var 0)      
       :&: evar 0 "z" ttt :=: evar 1 "arg" ttt
       :&: evar 1 "zola" tt :=: evar 0 "x@" tt
-- ∀: type .<( ∀: bool .<( ∀: 1 .<( ∀: 2 .<( 3 ≐ (77@fbody<3>:[ 3 ]  type) ( 0 )  

test4 :: Form       -- 0
test4 = Bind t -- 3 -- 2
                      -- 1
        $ Bind t -- 2 -- 1
                      -- 2
        $ Bind t -- 1 -- 0
                      -- 3
        $ Bind t -- 0
        $ var 3 :=: Pat (evvar 3 "x@" tt :+: var 0)      
       
-- should pass with "x" = \tt.1
test5 :: Form       -- 0
test5 = Bind t -- 3 -- 2
                    -- 1
      $ Bind t -- 2 -- 1
                    -- 2
      $ Bind t -- 1 -- 0
                    -- 3
      $ Bind t -- 0
                    -- 4
      $ evar 4 "x" tt_t :=: Abs tt (var 1)      
      
-- should pass with "x" = \tt.0
test6 :: Form       -- 0
test6 = evar 0 "x" tt_tt :=: Abs tt (var 0)            

test6N1 :: Form       -- 0
test6N1 = Bind tt 
        $ Pat (evvar 0 "x" tt_tt :+: var 0) :=: var 0            

test7 :: Form
test7 = ( Bind t -- 1
      $ Bind (vvar 0) -- 0 
      $ Pat (evvar 0 "x" (t ~> vvar 0 ~> vvar 1) :+: var 1 :+: var 0) :=: var 1 )
        
test8 :: Form
test8 = Bind t $
       ( Bind (vvar 0) -- 1
      $ Bind (vvar 0) -- 0 
      $ Pat (evvar 1 "x" (vvar 0  ~> vvar 0 ~> vvar 4) :+: var 1 :+: var 0) :=: var 1)        
       
test9 :: Form
test9 = Bind t
      $ Bind t
      $ Bind (vvar 1) -- 0 
      $ Pat (evvar 2 "x" (vvar 2  ~> t) :+: var 0) :=: Pat (vvar 2 ~> vvar 3)
      
test10 :: Form
test10 =  ( Bind t
          $ Pat (vvar 0 ~> t) :=: Pat (evvar 0 "f" tt :+: var 0)
          )
      :&: Pat (t ~> (evvar 0 "f" tt :+: var 0) ) :=: evar 0 "head" t
          
test t = case fst $ runState (runErrorT $ unifyAll newGraph constants t) (0 :: Int) of
  Right b -> snd b
  Left b -> error $ b


subA = Abs t 
     $ Abs (vvar 0) 
     $ Abs (vvar 1)
     $ Pat t
     
testSubA = hered' subA (var 0)
testSubB = (hered' (hered' subA (var 0)) (var 1))




