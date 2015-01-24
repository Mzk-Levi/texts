{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances, IncoherentInstances,
  KindSignatures, RankNTypes #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on higher-order difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Ops where

import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.HDitraversable
import qualified Data.Comp.Ops as O
import Control.Monad (liftM)


-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) (a :: * -> *) (b :: * -> *) i = Inl (f a b i)
                                             | Inr (g a b i)

{-| Utility function to case on a higher-order difunctor sum, without exposing
  the internal representation of sums. -}
caseHD :: (f a b i -> c) -> (g a b i -> c) -> (f :+: g) a b i -> c
caseHD f g x = case x of
                 Inl x -> f x
                 Inr x -> g x

instance (HDifunctor f, HDifunctor g) => HDifunctor (f :+: g) where
    hdimap f g (Inl e) = Inl (hdimap f g e)
    hdimap f g (Inr e) = Inr (hdimap f g e)

instance (HDitraversable f, HDitraversable g) => HDitraversable (f :+: g) where
    hdimapM f (Inl e) = Inl `liftM` hdimapM f e
    hdimapM f (Inr e) = Inr `liftM` hdimapM f e

-- | Signature containment relation for automatic injections. The left-hand must
-- be an atomic signature, where as the right-hand side must have a list-like
-- structure. Examples include @f :<: f :+: g@ and @g :<: f :+: (g :+: h)@,
-- non-examples include @f :+: g :<: f :+: (g :+: h)@ and
-- @f :<: (f :+: g) :+: h@.
class (sub :: (* -> *) -> (* -> *) -> * -> *) :<: sup where
    inj :: sub a b :-> sup a b
    proj :: NatM Maybe (sup a b) (sub a b)

instance (:<:) f f where
    inj = id
    proj = Just

instance (:<:) f (f :+: g) where
    inj = Inl
    proj (Inl x) = Just x
    proj (Inr _) = Nothing

instance (f :<: g) => (:<:) f (h :+: g) where
    inj = Inr . inj
    proj (Inr x) = proj x
    proj (Inl _) = Nothing


-- Products
infixr 8 :*:

-- |Formal product of signatures (higher-order difunctors).
data (f :*: g) a b = f a b :*: g a b

ffst :: (f :*: g) a b -> f a b
ffst (x :*: _) = x

fsnd :: (f :*: g) a b -> g a b 
fsnd (_ :*: x) = x


-- Constant Products
infixr 7 :&:

{-| This data type adds a constant product to a signature. -}
data (f :&: p) (a :: * -> *) (b :: * -> *) i = f a b i :&: p

instance HDifunctor f => HDifunctor (f :&: p) where
    hdimap f g (v :&: c) = hdimap f g v :&: c

instance HDitraversable f => HDitraversable (f :&: p) where
    hdimapM f (v :&: c) = liftM (:&: c) (hdimapM f v)

{-| This class defines how to distribute an annotation over a sum of
  signatures. -}
class DistAnn (s :: (* -> *) -> (* -> *) -> * -> *) p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a b :-> s' a b
    {-| Project an annotation from a signature. -}
    projectA :: s' a b :-> (s a b O.:&: p)

class RemA (s :: (* -> *) -> (* -> *) -> * -> *) s' | s -> s' where
    {-| Remove annotations from a signature. -}
    remA :: s a b :-> s' a b

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v

instance RemA (f :&: p) f where
    remA (v :&: _) = v

instance DistAnn f p (f :&: p) where
    injectA c v = v :&: c

    projectA (v :&: p) = v O.:&: p

instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = Inl v O.:&: p
    projectA (Inr v) = let (v' O.:&: p) = projectA v
                       in Inr v' O.:&: p
