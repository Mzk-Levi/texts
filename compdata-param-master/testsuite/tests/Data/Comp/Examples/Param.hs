{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples.Param where

import Examples.Names as Names
import Examples.Graph as Graph

import Data.Comp.Param

import Test.Framework
import Test.Framework.Providers.HUnit
import Test.HUnit






--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

tests = testGroup "Parametric Compositional Data Types" [
         testCase "names" namesTest,
         testCase "graph" graphTest
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

instance (EqD f, PEq p) => EqD (f :&: p) where
    eqD (v1 :&: p1) (v2 :&: p2) = do b1 <- peq p1 p2
                                     b2 <- eqD v1 v2
                                     return $ b1 && b2

namesTest = sequence_ [en @=? en', ep @=? ep']
graphTest = sequence_ [n @=? 5, f @=? [0,2,1,2]]
