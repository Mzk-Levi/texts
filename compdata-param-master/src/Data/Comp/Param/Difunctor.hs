{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Difunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines difunctors (Meijer, Hutton, FPCA '95), i.e. binary type
-- constructors that are contravariant in the first argument and covariant in
-- the second argument.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Difunctor
    (
      difmap,
     Difunctor(..)
    ) where

-- | This class represents difunctors, i.e. binary type constructors that are
-- contravariant in the first argument and covariant in the second argument.
class Difunctor f where
    dimap :: (a -> b) -> (c -> d) -> f b c -> f a d

{-| The canonical example of a difunctor. -}
instance Difunctor (->) where
    dimap f g h = g . h . f

difmap :: Difunctor f => (a -> b) -> f c a -> f c b
difmap = dimap id

instance Difunctor f => Functor (f a) where
    fmap = difmap