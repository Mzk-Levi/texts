{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP, KindSignatures #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Algebra
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the notion of algebras and catamorphisms, and their
-- generalizations to e.g. monadic versions and other (co)recursion schemes.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Algebra (
      -- * Algebras & Catamorphisms
      Alg,
      free,
      cata,
      cata',
      appCxt,
      
      -- * Monadic Algebras & Catamorphisms
      AlgM,
--      algM,
      freeM,
      cataM,
      AlgM',
      Compose(..),
      freeM',
      cataM',

      -- * Term Homomorphisms
      CxtFun,
      SigFun,
      Hom,
      appHom,
      appHom',
      compHom,
      appSigFun,
      appSigFun',
      compSigFun,
      hom,
      compAlg,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      HomM,
      sigFunM,
      hom',
      appHomM,
      appTHomM,
      appHomM',
      appTHomM',
      homM,
      appSigFunM,
      appTSigFunM,
      appSigFunM',
      appTSigFunM',
      compHomM,
      compSigFunM,
      compAlgM,
      compAlgM'
    ) where

import Prelude hiding (sequence, mapM)
import Control.Monad hiding (sequence, mapM)
import Data.Functor.Compose -- Functor composition
import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.HDitraversable

{-| This type represents an algebra over a difunctor @f@ and carrier @a@. -}
type Alg f a = f a a :-> a

{-| Construct a catamorphism for contexts over @f@ with holes of type @b@, from
  the given algebra. -}
free :: forall h f a b. HDifunctor f
        => Alg f a -> (b :-> a) -> Cxt h f a b :-> a
free f g = run
    where run :: Cxt h f a b :-> a
          run (In t) = f (hfmap run t)
          run (Hole x) = g x
          run (Var p) = p

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a. HDifunctor f => Alg f a -> Term f :-> a 
{-# NOINLINE [1] cata #-}
cata f (Term t) = run t
    where run :: Trm f a :-> a
          run (In t) = f (hfmap run t)
          run (Var x) = x

{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: HDifunctor f => Alg f a -> Cxt h f a a :-> a
{-# INLINE cata' #-}
cata' f = free f id

{-| This function applies a whole context into another context. -}
appCxt :: HDifunctor f => Cxt Hole f a (Cxt h f a b) :-> Cxt h f a b
appCxt (In t) = In (hfmap appCxt t)
appCxt (Hole x) = x
appCxt (Var p) = Var p

{-| This type represents a monadic algebra. It is similar to 'Alg' but
  the return type is monadic. -}
type AlgM m f a = NatM m (f a a) a

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM :: forall m h f a b. (HDitraversable f, Monad m)
         => AlgM m f a -> NatM m b a -> NatM m (Cxt h f a b) a
freeM f g = run
    where run :: NatM m (Cxt h f a b) a
          run (In t) = f =<< hdimapM run t
          run (Hole x) = g x
          run (Var p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: forall m f a. (HDitraversable f, Monad m)
         => AlgM m f a -> NatM m (Term f) a
{-# NOINLINE [1] cataM #-}
cataM algm (Term t) = run t
    where run :: NatM m (Trm f a) a
          run (In t) = algm =<< hdimapM run t
          run (Var x) = return x

{-| This type represents a monadic algebra, but where the covariant argument is
  also a monadic computation. -}
type AlgM' m f a = NatM m (f a (Compose m a)) a

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM' :: forall m h f a b. (HDifunctor f, Monad m)
          => AlgM' m f a -> NatM m b a -> NatM m (Cxt h f a b) a
freeM' f g = run
    where run :: NatM m (Cxt h f a b) a
          run (In t) = f $ hfmap (Compose . run) t
          run (Hole x) = g x
          run (Var p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM' :: forall m f a. (HDifunctor f, Monad m)
          => AlgM' m f a -> NatM m (Term f) a
{-# NOINLINE [1] cataM' #-}
cataM' algm (Term t) = run t
    where run :: NatM m (Trm f a) a
          run (In t) = algm $ hfmap (Compose . run) t
          run (Var x) = return x

{-| This type represents a signature function. -}
type SigFun f g = forall (a :: * -> *) (b :: * -> *) . f a b :-> g a b

{-| This type represents a context function. -}
type CxtFun f g = forall h. SigFun (Cxt h f) (Cxt h g)

{-| This type represents a term homomorphism. -}
type Hom f g = SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appHom :: forall f g. (HDifunctor f, HDifunctor g) => Hom f g -> CxtFun f g
{-# INLINE [1] appHom #-}
appHom f = run where
    run :: CxtFun f g
    run (In t) = appCxt (f (hfmap run t))
    run (Hole x) = Hole x
    run (Var p) = Var p

-- | Apply a term homomorphism recursively to a term/context. This is
-- a top-down variant of 'appHom'.
appHom' :: forall f g. (HDifunctor g)
              => Hom f g -> CxtFun f g
{-# INLINE [1] appHom' #-}
appHom' f = run where
    run :: CxtFun f g
    run (In t) = appCxt (hfmapCxt run (f t))
    run (Hole x) = Hole x
    run (Var p) = Var p

{-| Compose two term homomorphisms. -}
compHom :: (HDifunctor g, HDifunctor h)
               => Hom g h -> Hom f g -> Hom f h
compHom f g = appHom f . g

{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (HDifunctor f, HDifunctor g) => Alg g a -> Hom f g -> Alg f a
compAlg alg talg = cata' alg . talg

{-| This function applies a signature function to the given context. -}
appSigFun :: forall f g. (HDifunctor f) => SigFun f g -> CxtFun f g
appSigFun f = run where
    run :: CxtFun f g
    run (In t) = In (f (hfmap run t))
    run (Hole x) = Hole x
    run (Var p) = Var p

{-| This function applies a signature function to the given context. -}
appSigFun' :: forall f g. (HDifunctor g) => SigFun f g -> CxtFun f g
appSigFun' f = run where
    run :: CxtFun f g
    run (In t) = In (hfmap run (f t))
    run (Hole x) = Hole x
    run (Var p) = Var p

{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g

{-| Lifts the given signature function to the canonical term homomorphism. -}
hom :: HDifunctor g => SigFun f g -> Hom f g
hom f = simpCxt . f

{-| This type represents a monadic signature function. -}
type SigFunM m f g = forall (a :: * -> *) (b :: * -> *) . NatM m (f a b) (g a b)

{-| This type represents a monadic context function. -}
type CxtFunM m f g = forall h . SigFunM m (Cxt h f) (Cxt h g)

{-| This type represents a monadic term homomorphism. -}
type HomM m f g = SigFunM m f (Cxt Hole g)


{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the give monadic signature function to a monadic term homomorphism. -}
hom' :: (HDifunctor f, HDifunctor g, Monad m)
            => SigFunM m f g -> HomM m f g
hom' f = liftM  (In . hfmap Hole) . f

{-| Lift the given signature function to a monadic term homomorphism. -}
homM :: (HDifunctor g, Monad m) => SigFun f g -> HomM m f g
homM f = sigFunM $ hom f

{-| Apply a monadic term homomorphism recursively to a term/context. -}
appHomM :: forall f g m. (HDitraversable f, Monad m, HDifunctor g)
               => HomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appHomM #-}
appHomM f = run
    where run :: CxtFunM m f g
          run (In t) = liftM appCxt (f =<< hdimapM run t)
          run (Hole x) = return (Hole x)
          run (Var p) = return (Var p)

{-| A restricted form of |appHomM| which only works for terms. -}
appTHomM :: (HDitraversable f, Monad m, ParamFunctor m, HDifunctor g)
            => HomM m f g -> Term f i -> m (Term g i)
appTHomM f (Term t) = termM (appHomM f t)

-- | Apply a monadic term homomorphism recursively to a
-- term/context. This is a top-down variant of 'appHomM'.
appHomM' :: forall f g m. (HDitraversable g, Monad m)
            => HomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appHomM' #-}
appHomM' f = run
    where run :: CxtFunM m f g
          run (In t) = liftM appCxt (hdimapMCxt run =<<  f t)
          run (Hole x) = return (Hole x)
          run (Var p) = return (Var p)

{-| A restricted form of |appHomM'| which only works for terms. -}
appTHomM' :: (HDitraversable g, Monad m, ParamFunctor m, HDifunctor g)
             => HomM m f g -> Term f i -> m (Term g i)
appTHomM' f (Term t) = termM (appHomM' f t)

{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: forall m f g. (HDitraversable f, Monad m)
              => SigFunM m f g -> CxtFunM m f g
appSigFunM f = run
    where run :: CxtFunM m f g
          run (In t)   = liftM In (f =<< hdimapM run t)
          run (Hole x) = return (Hole x)
          run (Var p)  = return (Var p)

{-| A restricted form of |appSigFunM| which only works for terms. -}
appTSigFunM :: (HDitraversable f, Monad m, ParamFunctor m, HDifunctor g)
               => SigFunM m f g -> Term f i -> m (Term g i)
appTSigFunM f (Term t) = termM (appSigFunM f t)

-- | This function applies a monadic signature function to the given
-- context. This is a top-down variant of 'appSigFunM'.
appSigFunM' :: forall m f g. (HDitraversable g, Monad m)
               => SigFunM m f g -> CxtFunM m f g
appSigFunM' f = run
    where run :: CxtFunM m f g
          run (In t)   = liftM In (hdimapM run =<< f t)
          run (Hole x) = return (Hole x)
          run (Var p)  = return (Var p)

{-| A restricted form of |appSigFunM'| which only works for terms. -}
appTSigFunM' :: (HDitraversable g, Monad m, ParamFunctor m, HDifunctor g)
                => SigFunM m f g -> Term f i -> m (Term g i)
appTSigFunM' f (Term t) = termM (appSigFunM' f t)

{-| Compose two monadic term homomorphisms. -}
compHomM :: (HDitraversable g, HDifunctor h, Monad m)
                => HomM m g h -> HomM m f g -> HomM m f h
compHomM f g = appHomM f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (HDitraversable g, Monad m) => AlgM m g a -> HomM m f g -> AlgM m f a
compAlgM alg talg = freeM alg return <=< talg

{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (HDitraversable g, Monad m) => AlgM m g a -> Hom f g -> AlgM m f a
compAlgM' alg talg = freeM alg return . talg

{-| This function composes two monadic signature functions. -}
compSigFunM :: Monad m => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g a = g a >>= f

{-
#ifndef NO_RULES
{-# RULES
  "cata/appHom" forall (a :: Alg g d) (h :: Hom f g) x.
    cata a (appHom h x) = cata (compAlg a h) x;

  "appHom/appHom" forall (a :: Hom g h) (h :: Hom f g) x.
    appHom a (appHom h x) = appHom (compHom a h) x; #-}

{-
{-# RULES 
  "cataM/appHomM" forall (a :: AlgM m g d) (h :: HomM m f g d) x.
     appHomM h x >>= cataM a = cataM (compAlgM a h) x;

  "cataM/appHom" forall (a :: AlgM m g d) (h :: Hom f g) x.
     cataM a (appHom h x) = cataM (compAlgM' a h) x;

  "appHomM/appHomM" forall (a :: HomM m g h b) (h :: HomM m f g b) x.
    appHomM h x >>= appHomM a = appHomM (compHomM a h) x; #-}

{-# RULES
  "cata/build"  forall alg (g :: forall a . Alg f a -> a) .
                cata alg (build g) = g alg #-}
-}
#endif
-}
