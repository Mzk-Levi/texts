{-# LANGUAGE TemplateHaskell, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, OverlappingInstances, Rank2Types, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines the 'Desugar' type class for desugaring of terms.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Desugar where

import Data.Comp.Param


-- |The desugaring term homomorphism.
class (Difunctor f, Difunctor g) => Desugar f g where
    desugHom :: Hom f g
    desugHom = desugHom' . fmap Hole
    desugHom' :: f a (Cxt h g a b) -> Cxt h g a b
    desugHom' x = appCxt (desugHom x)

-- We make the lifting to sums explicit in order to make the Desugar
-- class work with the default instance declaration further below.
instance (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
    desugHom = caseD desugHom desugHom

-- |Desugar a term.
desugar :: Desugar f g => Term f -> Term g
{-# INLINE desugar #-}
desugar (Term t) = Term (appHom desugHom t)

-- |Lift desugaring to annotated terms.
desugarA :: (Difunctor f', Difunctor g', DistAnn f p f', DistAnn g p g',
             Desugar f g) => Term f' -> Term g'
desugarA (Term t) = Term (appHom (propAnn desugHom) t)

-- |Default desugaring instance.
instance (Difunctor f, Difunctor g, f :<: g) => Desugar f g where
    desugHom = simpCxt . inj