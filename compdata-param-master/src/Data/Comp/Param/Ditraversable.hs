{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ditraversable
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines traversable difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Ditraversable
    (
     Ditraversable(..)
    ) where

import Data.Comp.Param.Difunctor

{-| Difunctors representing data structures that can be traversed from left to
  right. -}
class Difunctor f => Ditraversable f where
    dimapM :: Monad m => (b -> m c) -> f a b -> m (f a c)
    dimapM f = disequence . fmap f
    disequence :: Monad m => f a (m b) -> m (f a b)
    disequence = dimapM id