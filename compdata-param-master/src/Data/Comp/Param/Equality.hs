{-# LANGUAGE TypeOperators, TypeSynonymInstances, FlexibleInstances,
  UndecidableInstances, IncoherentInstances, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Equality
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
module Data.Comp.Param.Equality
    (
     PEq(..),
     EqD(..)
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.FreshM
import Control.Monad (liftM)

-- |Equality on parametric values. The equality test is performed inside the
-- 'FreshM' monad for generating fresh identifiers.
class PEq a where
    peq :: a -> a -> FreshM Bool

instance PEq a => PEq [a] where
    peq l1 l2
        | length l1 /= length l2 = return False
        | otherwise = liftM or $ mapM (uncurry peq) $ zip l1 l2

instance Eq a => PEq a where
    peq x y = return $ x == y

{-| Signature equality. An instance @EqD f@ gives rise to an instance
  @Eq (Term f)@. The equality test is performed inside the 'FreshM' monad for
  generating fresh identifiers. -}
class EqD f where
    eqD :: PEq a => f Name a -> f Name a -> FreshM Bool

{-| 'EqD' is propagated through sums. -}
instance (EqD f, EqD g) => EqD (f :+: g) where
    eqD (Inl x) (Inl y) = eqD x y
    eqD (Inr x) (Inr y) = eqD x y
    eqD _ _ = return False

{-| From an 'EqD' difunctor an 'Eq' instance of the corresponding term type can
  be derived. -}
instance EqD f => EqD (Cxt h f) where
    eqD (In e1) (In e2) = eqD e1 e2
    eqD (Hole h1) (Hole h2) = peq h1 h2
    eqD (Var p1) (Var p2) = peq p1 p2
    eqD _ _ = return False

instance (EqD f, PEq a) => PEq (Cxt h f Name a) where
    peq = eqD

{-| Equality on terms. -}
instance (Difunctor f, EqD f) => Eq (Term f) where
    (==) (Term x) (Term y) = evalFreshM $ eqD x y