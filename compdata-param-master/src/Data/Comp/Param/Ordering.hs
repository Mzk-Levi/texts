{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ordering
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
module Data.Comp.Param.Ordering
    (
     POrd(..),
     OrdD(..),
     compList
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.FreshM
import Data.Comp.Param.Equality
import Data.Maybe (fromMaybe)
import Data.List (find)
import Control.Monad (liftM)

-- |Ordering of parametric values.
class PEq a => POrd a where
    pcompare :: a -> a -> FreshM Ordering

instance POrd a => POrd [a] where
    pcompare l1 l2
        | length l1 < length l2 = return LT
        | length l1 > length l2 = return GT
        | otherwise = liftM compList $ mapM (uncurry pcompare) $ zip l1 l2

compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

instance Ord a => POrd a where
    pcompare x y = return $ compare x y

{-| Signature ordering. An instance @OrdD f@ gives rise to an instance
  @Ord (Term f)@. -}
class EqD f => OrdD f where
    compareD :: POrd a => f Name a -> f Name a -> FreshM Ordering

{-| 'OrdD' is propagated through sums. -}
instance (OrdD f, OrdD g) => OrdD (f :+: g) where
    compareD (Inl x) (Inl y) = compareD x y
    compareD (Inl _) (Inr _) = return LT
    compareD (Inr x) (Inr y) = compareD x y
    compareD (Inr _) (Inl _) = return GT

{-| From an 'OrdD' difunctor an 'Ord' instance of the corresponding term type
  can be derived. -}
instance OrdD f => OrdD (Cxt h f) where
    compareD (In e1) (In e2) = compareD e1 e2
    compareD (Hole h1) (Hole h2) = pcompare h1 h2
    compareD (Var p1) (Var p2) = pcompare p1 p2
    compareD (In _) _ = return LT
    compareD (Hole _) (In _) = return GT
    compareD (Hole _) (Var _) = return LT
    compareD (Var _) _ = return GT

instance (OrdD f, POrd a) => POrd (Cxt h f Name a) where
    pcompare = compareD

{-| Ordering of terms. -}
instance (Difunctor f, OrdD f) => Ord (Term f) where
    compare (Term x) (Term y) = evalFreshM $ compareD x y