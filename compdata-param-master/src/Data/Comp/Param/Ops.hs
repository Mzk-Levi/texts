{-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies,
  FlexibleInstances, UndecidableInstances, IncoherentInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Ops
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module provides operators on difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Ops where

import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable
import Control.Monad (liftM)


-- Sums
infixr 6 :+:

-- |Formal sum of signatures (difunctors).
data (f :+: g) a b = Inl (f a b)
                   | Inr (g a b)

{-| Utility function to case on a difunctor sum, without exposing the internal
  representation of sums. -}
caseD :: (f a b -> c) -> (g a b -> c) -> (f :+: g) a b -> c
caseD f g x = case x of
                Inl x -> f x
                Inr x -> g x

instance (Difunctor f, Difunctor g) => Difunctor (f :+: g) where
    dimap f g (Inl e) = Inl (dimap f g e)
    dimap f g (Inr e) = Inr (dimap f g e)

instance (Ditraversable f, Ditraversable g) => Ditraversable (f :+: g) where
    dimapM f (Inl e) = Inl `liftM` dimapM f e
    dimapM f (Inr e) = Inr `liftM` dimapM f e
    disequence (Inl e) = Inl `liftM` disequence e
    disequence (Inr e) = Inr `liftM` disequence e

-- | Signature containment relation for automatic injections. The left-hand must
-- be an atomic signature, where as the right-hand side must have a list-like
-- structure. Examples include @f :<: f :+: g@ and @g :<: f :+: (g :+: h)@,
-- non-examples include @f :+: g :<: f :+: (g :+: h)@ and
-- @f :<: (f :+: g) :+: h@.
class sub :<: sup where
  inj :: sub a b -> sup a b
  proj :: sup a b -> Maybe (sub a b)

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

-- |Formal product of signatures (difunctors).
data (f :*: g) a b = f a b :*: g a b

ffst :: (f :*: g) a b -> f a b
ffst (x :*: _) = x

fsnd :: (f :*: g) a b -> g a b
fsnd (_ :*: x) = x


-- Constant Products
infixr 7 :&:

{-| This data type adds a constant product to a signature. -}
data (f :&: p) a b = f a b :&: p

instance Difunctor f => Difunctor (f :&: p) where
    dimap f g (v :&: c) = dimap f g v :&: c

instance Ditraversable f => Ditraversable (f :&: p) where
    dimapM f (v :&: c) = liftM (:&: c) (dimapM f v)
    disequence (v :&: c) = liftM (:&: c) (disequence v)

{-| This class defines how to distribute an annotation over a sum of
  signatures. -}
class DistAnn s p s' | s' -> s, s' -> p where
    {-| Inject an annotation over a signature. -}
    injectA :: p -> s a b -> s' a b
    {-| Project an annotation from a signature. -}
    projectA :: s' a b -> (s a b, p)

class RemA s s' | s -> s'  where
    {-| Remove annotations from a signature. -}
    remA :: s a b -> s' a b

instance (RemA s s') => RemA (f :&: p :+: s) (f :+: s') where
    remA (Inl (v :&: _)) = Inl v
    remA (Inr v) = Inr $ remA v

instance RemA (f :&: p) f where
    remA (v :&: _) = v

instance DistAnn f p (f :&: p) where
    injectA c v = v :&: c

    projectA (v :&: p) = (v,p)

instance (DistAnn s p s') => DistAnn (f :+: s) p ((f :&: p) :+: s') where
    injectA c (Inl v) = Inl (v :&: c)
    injectA c (Inr v) = Inr $ injectA c v

    projectA (Inl (v :&: p)) = (Inl v,p)
    projectA (Inr v) = let (v',p) = projectA v
                       in  (Inr v',p)