{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines ordering of signatures, which lifts to ordering of
-- terms and contexts.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi.Ordering
    (
     POrd(..),
     OrdHD(..)
    ) where

import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.Sum
import Data.Comp.Param.Multi.Ops
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.FreshM
import Data.Comp.Param.Multi.Equality

-- |Ordering of parametric values.
class PEq a => POrd a where
    pcompare :: a i -> a j -> FreshM Ordering

instance Ord a => POrd (K a) where
    pcompare (K x) (K y) = return $ compare x y

{-| Signature ordering. An instance @OrdHD f@ gives rise to an instance
  @Ord (Term f)@. -}
class EqHD f => OrdHD f where
    compareHD :: POrd a => f Name a i -> f Name a j -> FreshM Ordering

{-| 'OrdHD' is propagated through sums. -}
instance (OrdHD f, OrdHD g) => OrdHD (f :+: g) where
    compareHD (Inl x) (Inl y) = compareHD x y
    compareHD (Inl _) (Inr _) = return LT
    compareHD (Inr x) (Inr y) = compareHD x y
    compareHD (Inr _) (Inl _) = return GT

{-| From an 'OrdHD' difunctor an 'Ord' instance of the corresponding term type
  can be derived. -}
instance OrdHD f => OrdHD (Cxt h f) where
    compareHD (In e1) (In e2) = compareHD e1 e2
    compareHD (Hole h1) (Hole h2) = pcompare h1 h2
    compareHD (Var p1) (Var p2) = pcompare p1 p2
    compareHD (In _) _ = return LT
    compareHD (Hole _) (In _) = return GT
    compareHD (Hole _) (Var _) = return LT
    compareHD (Var _) _ = return GT

instance POrd Name where
    pcompare x y = return $ compare (nameCoerce x) y

instance (OrdHD f, POrd a) => POrd (Cxt h f Name a) where
    pcompare = compareHD

{-| Ordering of terms. -}
instance (HDifunctor f, OrdHD f) => Ord (Term f i) where
    compare (Term x) (Term y) = evalFreshM $ compareHD x y
