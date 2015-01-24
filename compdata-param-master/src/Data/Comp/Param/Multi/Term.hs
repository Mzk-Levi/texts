{-# LANGUAGE EmptyDataDecls, GADTs, KindSignatures, Rank2Types,
  MultiParamTypeClasses, TypeOperators, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Term
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the central notion of /generalised parametrised terms/
-- and their generalisation to generalised parametrised contexts.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Term
    (
     Cxt(..),
     Hole,
     NoHole,
     Term(..),
     Trm,
     Context,
     simpCxt,
     toCxt,
     hfmapCxt,
     hdimapMCxt,
     ParamFunctor (..)
    ) where

import Prelude hiding (mapM, sequence, foldl, foldl1, foldr, foldr1)
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.HDitraversable
import Control.Monad 
import Unsafe.Coerce
import Data.Maybe (fromJust)

{-| This data type represents contexts over a signature. Contexts are terms
  containing zero or more holes, and zero or more parameters. The first
  parameter is a phantom type indicating whether the context has holes. The
  second paramater is the signature of the context, in the form of a
  "Data.Comp.Param.Multi.HDifunctor". The third parameter is the type of
  parameters, the fourth parameter is the type of holes, and the fifth
  parameter is the GADT type. -}
data Cxt :: * -> ((* -> *) -> (* -> *) -> * -> *) -> (* -> *) -> (* -> *) -> * -> * where
            In :: f a (Cxt h f a b) i -> Cxt h f a b i
            Hole :: b i -> Cxt Hole f a b i
            Var :: a i -> Cxt h f a b i

{-| Phantom type used to define 'Context'. -}
data Hole

{-| Phantom type used to define 'Term'. -}
data NoHole

{-| A context may contain holes. -}
type Context = Cxt Hole

{-| \"Preterms\" |-}
type Trm f a = Cxt NoHole f a (K ())

{-| A term is a context with no holes, where all occurrences of the
  contravariant parameter is fully parametric. -}
newtype Term f i = Term{unTerm :: forall a. Trm f a i}

{-| Convert a difunctorial value into a context. -}
simpCxt :: HDifunctor f => f a b :-> Cxt Hole f a b
{-# INLINE simpCxt #-}
simpCxt = In . hfmap Hole

toCxt :: HDifunctor f => Trm f a :-> Cxt h f a b
{-# INLINE toCxt #-}
toCxt = unsafeCoerce

-- | This is an instance of 'hfmap' for 'Cxt'.
hfmapCxt :: forall h f a b b'. HDifunctor f
         => (b :-> b') -> Cxt h f a b :-> Cxt h f a b'
hfmapCxt f = run
    where run :: Cxt h f a b :-> Cxt h f a b'
          run (In t)   = In $ hfmap run t
          run (Var a)  = Var a
          run (Hole b) = Hole $ f b

-- | This is an instance of 'hdimapM' for 'Cxt'.
hdimapMCxt :: forall h f a b b' m . (HDitraversable f, Monad m)
          => NatM m b b' -> NatM m (Cxt h f a b) (Cxt h f a b')
hdimapMCxt f = run
    where run :: NatM m (Cxt h f a b) (Cxt h f a b')
          run (In t)   = liftM In $ hdimapM run t
          run (Var a)  = return $ Var a
          run (Hole b) = liftM Hole (f b)
          
          
          
{-| Monads for which embedded @Trm@ values, which are parametric at top level,
  can be made into monadic @Term@ values, i.e. \"pushing the parametricity
  inwards\". -}
class ParamFunctor m where
    termM :: (forall a. m (Trm f a i)) -> m (Term f i)

coerceTermM :: ParamFunctor m => (forall a. m (Trm f a i)) -> m (Term f i)
{-# INLINE coerceTermM #-}
coerceTermM t = unsafeCoerce t

{-# RULES
    "termM/coerce'" termM = coerceTermM
 #-}

instance ParamFunctor Maybe where
    {-# NOINLINE [1] termM #-}
    termM Nothing = Nothing
    termM x       = Just (Term $ fromJust x)

instance ParamFunctor (Either a) where
    {-# NOINLINE [1] termM #-}
    termM (Left x) = Left x
    termM x        = Right (Term $ fromRight x)
                             where fromRight :: Either a b -> b
                                   fromRight (Right x) = x
                                   fromRight _ = error "fromRight: Left"

instance ParamFunctor [] where
    {-# NOINLINE [1] termM #-}
    termM [] = []
    termM l  = Term (head l) : termM (tail l)
