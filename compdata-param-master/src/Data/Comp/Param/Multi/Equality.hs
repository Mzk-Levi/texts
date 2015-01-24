{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Equality
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines equality for signatures, which lifts to equality for
-- terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi.Equality
    (
     PEq(..),
     EqHD(..)
    ) where

import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.Sum
import Data.Comp.Param.Multi.Ops
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.FreshM

-- |Equality on parametric values. The equality test is performed inside the
-- 'FreshM' monad for generating fresh identifiers.
class PEq a where
    peq :: a i -> a j -> FreshM Bool

instance Eq a => PEq (K a) where
    peq (K x) (K y) = return $ x == y

{-| Signature equality. An instance @EqHD f@ gives rise to an instance
  @Eq (Term f i)@. The equality test is performed inside the 'FreshM' monad for
  generating fresh identifiers. -}
class EqHD f where
    eqHD :: PEq a => f Name a i -> f Name a j -> FreshM Bool

{-| 'EqHD' is propagated through sums. -}
instance (EqHD f, EqHD g) => EqHD (f :+: g) where
    eqHD (Inl x) (Inl y) = eqHD x y
    eqHD (Inr x) (Inr y) = eqHD x y
    eqHD _ _ = return False

instance PEq Name where
   peq x y = return $ nameCoerce x == y

{-| From an 'EqHD' difunctor an 'Eq' instance of the corresponding term type can
  be derived. -}
instance EqHD f => EqHD (Cxt h f) where
    eqHD (In e1) (In e2) = eqHD e1 e2
    eqHD (Hole h1) (Hole h2) = peq h1 h2
    eqHD (Var p1) (Var p2) = peq p1 p2
    eqHD _ _ = return False

instance (EqHD f, PEq a) => PEq (Cxt h f Name a) where
    peq = eqHD

{-| Equality on terms. -}
instance (HDifunctor f, EqHD f) => Eq (Term f i) where
    (==) (Term x) (Term y) = evalFreshM $ eqHD x y
