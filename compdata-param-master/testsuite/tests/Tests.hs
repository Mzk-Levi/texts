module Main where

import Test.Framework
import qualified Data.Comp.Examples_Test

--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Data.Comp" [
         Data.Comp.Examples_Test.tests
       ]

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------
