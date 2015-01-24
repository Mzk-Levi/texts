{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, Rank2Types,
  TypeOperators, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines higher-order difunctors, a hybrid between higher-order
-- functors (Johann, Ghani, POPL '08), and difunctors (Meijer, Hutton, FPCA
-- '95). Higher-order difunctors are used to define signatures for
-- compositional parametric generalised data types.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.HDifunctor
    (
     HDifunctor (..),
     HFunctor (..),
     I (..),
     K (..),
     E (..),
     A (..),
     (:->),
     NatM
    ) where

import Data.Comp.Multi.HFunctor

-- | This class represents higher-order difunctors.
class HDifunctor f where
    hdimap :: (a :-> b) -> (c :-> d) -> f b c :-> f a d

-- |A higher-order difunctor gives rise to a higher-order functor when
-- restricted to a particular contravariant argument.
instance HDifunctor f => HFunctor (f a) where
    hfmap = hdimap id
