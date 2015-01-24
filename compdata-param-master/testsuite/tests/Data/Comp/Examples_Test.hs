{-# LANGUAGE TypeOperators #-}
module Data.Comp.Examples_Test where

import qualified Data.Comp.Examples.Param as P
import qualified Data.Comp.Examples.MultiParam as MP

import Test.Framework

tests = testGroup "Examples" [
         P.tests,
         MP.tests
       ]
