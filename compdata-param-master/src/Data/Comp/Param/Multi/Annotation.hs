{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FlexibleInstances,
  UndecidableInstances, Rank2Types, GADTs, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Annotation
-- Copyright   :  (c) 2010-2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Annotation
    (
     (:&:) (..),
     (:*:) (..),
     DistAnn (..),
     RemA (..),
     liftA,
     liftA',
     stripA,
     propAnn,
     propAnnM,
     ann,
     project'
    ) where

import qualified Data.Comp.Ops as O
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.Sum
import Data.Comp.Param.Multi.Ops
import Data.Comp.Param.Multi.Algebra

import Control.Monad

{-| Transform a function with a domain constructed from a higher-order difunctor
  to a function with a domain constructed with the same higher-order difunctor,
  but with an additional annotation. -}
liftA :: (RemA s s') => (s' a b :-> t) -> s a b :-> t
liftA f v = f (remA v)

{-| Transform a function with a domain constructed from a higher-order difunctor
  to a function with a domain constructed with the same higher-order difunctor,
  but with an additional annotation. -}
liftA' :: (DistAnn s' p s, HDifunctor s')
          => (s' a b :-> Cxt h s' c d) -> s a b :-> Cxt h s c d
liftA' f v = let v' O.:&: p = projectA v
             in ann p (f v')

{-| Strip the annotations from a term over a higher-order difunctor with
  annotations. -}
stripA :: (RemA g f, HDifunctor g) => CxtFun g f
stripA = appSigFun remA

{-| Lift a term homomorphism over signatures @f@ and @g@ to a term homomorphism
 over the same signatures, but extended with annotations. -}
propAnn :: (DistAnn f p f', DistAnn g p g', HDifunctor g) 
           => Hom f g -> Hom f' g'
propAnn hom f' = ann p (hom f)
    where f O.:&: p = projectA f'

{-| Lift a monadic term homomorphism over signatures @f@ and @g@ to a monadic
  term homomorphism over the same signatures, but extended with annotations. -}
propAnnM :: (DistAnn f p f', DistAnn g p g', HDifunctor g, Monad m)
         => HomM m f g -> HomM m f' g'
propAnnM hom f' = liftM (ann p) (hom f)
    where f O.:&: p = projectA f'

{-| Annotate each node of a term with a constant value. -}
ann :: (DistAnn f p g, HDifunctor f) => p -> CxtFun f g
ann c = appSigFun (injectA c)

{-| This function is similar to 'project' but applies to signatures
  with an annotation which is then ignored. -}
project' :: (RemA f f', s :<: f') => Cxt h f a b i -> Maybe (s a (Cxt h f a b) i)
project' (In x) = proj $ remA x
project' _ = Nothing
