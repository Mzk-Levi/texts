{-# LANGUAGE TypeOperators, MultiParamTypeClasses, TemplateHaskell,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Graph
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Graph representation. The example is taken from (Fegaras and Sheard,
-- Revisiting Catamorphisms over Datatypes with Embedded Functions, '96).
--
--------------------------------------------------------------------------------

module Examples.Graph where

import Data.Comp.Param
import Data.Comp.Param.Derive
import Data.Comp.Param.Show ()
import Data.Comp.Param.Equality ()

data N p a b = N p [b] -- Node
data R a b = R (a -> b) -- Recursion
data S a b = S (a -> b) b -- Sharing

$(derive [makeDifunctor, makeShowD, makeEqD, makeOrdD, smartConstructors]
         [''N, ''R, ''S])
$(derive [makeDitraversable] [''N])

type Graph p = Term (N p :+: R :+: S)

class FlatG f p where
  flatGAlg :: Alg f [p]

$(derive [liftSum] [''FlatG])

flatG :: (Difunctor f, FlatG f p) => Term f -> [p]
flatG = cata flatGAlg

instance FlatG (N p) p where
  flatGAlg (N p ps) = p : concat ps

instance FlatG R p where
  flatGAlg (R f) = f []

instance FlatG S p where
  flatGAlg (S f g) = f g

class SumG f where
  sumGAlg :: Alg f Int

$(derive [liftSum] [''SumG])

sumG :: (Difunctor f, SumG f) => Term f -> Int
sumG = cata sumGAlg

instance SumG (N Int) where
  sumGAlg (N p ps) = p + sum ps

instance SumG R where
  sumGAlg (R f) = f 0

instance SumG S where
  sumGAlg (S f g) = f g

g :: Graph Int
g = Term $ iR (\x -> iS (\z -> iN (0 :: Int) [z,iR $ \y -> iN (1 :: Int) [y,z]])
                        (iN (2 :: Int) [x]))

f :: [Int]
f = flatG g

n :: Int
n = sumG g
