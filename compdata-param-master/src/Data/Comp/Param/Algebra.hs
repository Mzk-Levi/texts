{-# LANGUAGE GADTs, Rank2Types, ScopedTypeVariables, TypeOperators,
  FlexibleContexts, CPP #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Algebra
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

module Data.Comp.Param.Algebra (
      -- * Algebras & Catamorphisms
      Alg,
      free,
      cata,
      cata',
      appCxt,
      
      -- * Monadic Algebras & Catamorphisms
      AlgM,
      algM,
      freeM,
      cataM,
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
      compHomSigFun,
      compSigFunHom,
      hom,
      compAlg,
      compAlgSigFun,

      -- * Monadic Term Homomorphisms
      CxtFunM,
      SigFunM,
      HomM,
      SigFunMD,
      HomMD,
      sigFunM,
      appHomM,
      appTHomM,
      appHomM',
      appTHomM',
      homM,
      homMD,
      appSigFunM,
      appTSigFunM,
      appSigFunM',
      appTSigFunM',
      appSigFunMD,
      appTSigFunMD,
      compHomM,
      compHomM',
      compSigFunM,
      compSigFunHomM,
      compSigFunHomM',
      compAlgSigFunM,
      compAlgSigFunM',
      compAlgM,
      compAlgM',

      -- * Coalgebras & Anamorphisms
      Coalg,
      ana,
      CoalgM,
      anaM,

      -- * R-Algebras & Paramorphisms
      RAlg,
      para,
      RAlgM,
      paraM,

      -- * R-Coalgebras & Apomorphisms
      RCoalg,
      apo,
      RCoalgM,
      apoM,

      -- * CV-Algebras & Histomorphisms
      CVAlg,
      histo,
      CVAlgM,
      histoM,

      -- * CV-Coalgebras & Futumorphisms
      CVCoalg,
      futu,
      CVCoalg',
      futu',
      CVCoalgM,
      futuM
    ) where

import Prelude hiding (sequence, mapM)
import Control.Monad hiding (sequence, mapM)
import Data.Comp.Param.Term
import Data.Comp.Param.Ops
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Ditraversable

{-| This type represents an algebra over a difunctor @f@ and carrier @a@. -}
type Alg f a = f a a -> a


{-| Construct a catamorphism for contexts over @f@ with holes of type @b@, from
  the given algebra. -}
free :: forall h f a b. Difunctor f
        => Alg f a -> (b -> a) -> Cxt h f a b -> a
free f g = run
    where run :: Cxt h f a b -> a
          run (In t) = f (difmap run t)
          run (Hole x) = g x
          run (Var p) = p

{-| Construct a catamorphism from the given algebra. -}
cata :: forall f a. Difunctor f => Alg f a -> Term f -> a 
{-# NOINLINE [1] cata #-}
cata f (Term t) = run t
    where run :: Trm f a -> a
          run (In t) = f (difmap run t)
          run (Var x) = x

{-| A generalisation of 'cata' from terms over @f@ to contexts over @f@, where
  the holes have the type of the algebra carrier. -}
cata' :: Difunctor f => Alg f a -> Cxt h f a a -> a
{-# INLINE cata' #-}
cata' f = free f id

{-| This function applies a whole context into another context. -}
appCxt :: Difunctor f => Context f a (Cxt h f a b) -> Cxt h f a b
appCxt (In t) = In (difmap appCxt t)
appCxt (Hole x) = x
appCxt (Var p) = Var p

{-| This type represents a monadic algebra. It is similar to 'Alg' but
  the return type is monadic. -}
type AlgM m f a = f a a -> m a

{-| Convert a monadic algebra into an ordinary algebra with a monadic
  carrier. -}
algM :: (Ditraversable f, Monad m) => AlgM m f a -> Alg f (m a)
algM f x = disequence (dimap return id x) >>= f

{-| Construct a monadic catamorphism for contexts over @f@ with holes of type
  @b@, from the given monadic algebra. -}
freeM :: forall m h f a b. (Ditraversable f, Monad m)
         => AlgM m f a -> (b -> m a) -> Cxt h f a b -> m a
freeM f g = run
    where run :: Cxt h f a b -> m a
          run (In t) = f =<< dimapM run t
          run (Hole x) = g x
          run (Var p) = return p

{-| Construct a monadic catamorphism from the given monadic algebra. -}
cataM :: forall m f a. (Ditraversable f, Monad m) => AlgM m f a -> Term f -> m a
{-# NOINLINE [1] cataM #-}
cataM algm (Term t) = run t
    where run :: Trm f a  -> m a
          run (In t) = algm =<< dimapM run t
          run (Var x) = return x

{-| A generalisation of 'cataM' from terms over @f@ to contexts over @f@, where
  the holes have the type of the monadic algebra carrier. -}
cataM' :: forall m h f a. (Ditraversable f, Monad m)
          => AlgM m f a -> Cxt h f a (m a) -> m a
{-# NOINLINE [1] cataM' #-}
cataM' f = freeM f id

{-| This type represents a context function. -}
type CxtFun f g = forall h a b. Cxt h f a b -> Cxt h g a b


{-| This type represents a signature function. -}
type SigFun f g = forall a b. f a b -> g a b

{-| This type represents a term homomorphism. -}
type Hom f g = SigFun f (Context g)

{-| Apply a term homomorphism recursively to a term/context. -}
appHom :: forall f g. (Difunctor f, Difunctor g) => Hom f g -> CxtFun f g
{-# NOINLINE [1] appHom #-}
appHom f = run where
    run :: CxtFun f g
    run (In t) = appCxt (f (difmap run t))
    run (Hole x) = Hole x
    run (Var p) = Var p

{-| Apply a term homomorphism recursively to a term/context. -}
appHom' :: forall f g. (Difunctor g) => Hom f g -> CxtFun f g
{-# NOINLINE [1] appHom' #-}
appHom' f = run where
    run :: CxtFun f g
    run (In t) = appCxt (fmapCxt run (f t))
    run (Hole x) = Hole x
    run (Var p) = Var p

fmapCxt :: Difunctor f => (b -> b') -> Cxt h f a b -> Cxt h f a b'
fmapCxt f = run
    where run (In t) = In $ difmap run t
          run (Var a) = Var a
          run (Hole b)  = Hole $ f b

{-| Compose two term homomorphisms. -}
compHom :: (Difunctor g, Difunctor h)
               => Hom g h -> Hom f g -> Hom f h
compHom f g = appHom f . g


{-| Compose an algebra with a term homomorphism to get a new algebra. -}
compAlg :: (Difunctor f, Difunctor g) => Alg g a -> Hom f g -> Alg f a
compAlg alg talg = cata' alg . talg

compAlgSigFun  :: Alg g a -> SigFun f g -> Alg f a
compAlgSigFun alg sig = alg . sig


{-| This function applies a signature function to the given context. -}
appSigFun :: forall f g. (Difunctor f) => SigFun f g -> CxtFun f g
{-# NOINLINE [1] appSigFun #-}
appSigFun f = run
    where run (In t) = In $ f $ difmap run t
          run (Var x) = Var x
          run (Hole x) = Hole x
-- implementation via term homomorphisms
--  appSigFun f = appHom $ hom f


-- | This function applies a signature function to the given
-- context. This is a top-bottom variant of 'appSigFun'.
appSigFun' :: forall f g. (Difunctor g) => SigFun f g -> CxtFun f g
{-# NOINLINE [1] appSigFun' #-}
appSigFun' f = run
    where run (In t) = In $ difmap run $ f t
          run (Var x) = Var x
          run (Hole x) = Hole x

{-| This function composes two signature functions. -}
compSigFun :: SigFun g h -> SigFun f g -> SigFun f h
compSigFun f g = f . g

{-| This function composes a term homomorphism and a signature function. -}
compHomSigFun :: Hom g h -> SigFun f g -> Hom f h
compHomSigFun f g = f . g

{-| This function composes a term homomorphism and a signature function. -}
compSigFunHom :: (Difunctor g) => SigFun g h -> Hom f g -> Hom f h
compSigFunHom f g = appSigFun f . g


{-| Lifts the given signature function to the canonical term homomorphism. -}
hom :: Difunctor g => SigFun f g -> Hom f g
hom f = simpCxt . f

{-| This type represents a monadic signature function. -}
type SigFunM m f g = forall a b. f a b -> m (g a b)

{-| This type represents a monadic context function. -}
type CxtFunM m f g = forall h . SigFunM m (Cxt h f) (Cxt h g)

{-| This type represents a monadic signature function. It is similar to
  'SigFunM' but has monadic values also in the domain. -}
type SigFunMD m f g = forall a b. f a (m b) -> m (g a b)

{-| This type represents a monadic term homomorphism. -}
type HomM m f g = SigFunM m f (Context g)

{-| This type represents a monadic term homomorphism. It is similar to
  'HomM' but has monadic values also in the domain. -}
type HomMD m f g = SigFunMD m f (Context g)

{-| Lift the given signature function to a monadic signature function. Note that
  term homomorphisms are instances of signature functions. Hence this function
  also applies to term homomorphisms. -}
sigFunM :: Monad m => SigFun f g -> SigFunM m f g
sigFunM f = return . f

{-| Lift the given signature function to a monadic term homomorphism. -}
homM :: (Difunctor g, Monad m) => SigFunM m f g -> HomM m f g
homM f = liftM simpCxt . f

-- | Apply a monadic term homomorphism recursively to a
-- term/context. The monad is sequenced bottom-up.
appHomM :: forall f g m. (Ditraversable f, Difunctor g, Monad m)
           => HomM m f g -> CxtFunM m f g
{-# NOINLINE [1] appHomM #-}
appHomM f = run
    where run :: CxtFunM m f g
          run (In t) = liftM appCxt . f =<< dimapM run t
          run (Hole x) = return (Hole x)
          run (Var p) = return (Var p)

{-| A restricted form of |appHomM| which only works for terms. -}
appTHomM :: (Ditraversable f, ParamFunctor m, Monad m, Difunctor g)
            => HomM m f g -> Term f -> m (Term g)
appTHomM f (Term t) = termM (appHomM f t)


-- | Apply a monadic term homomorphism recursively to a
-- term/context. The monad is sequence top-down.
appHomM' :: forall f g m. (Ditraversable g, Monad m)
            => HomM m f g -> CxtFunM m f g
appHomM' f = run
    where run :: CxtFunM m f g
          run (In t)  = liftM appCxt . dimapMCxt run =<< f t
          run (Var p) = return (Var p)
          run (Hole x) = return (Hole x)

dimapMCxt :: (Ditraversable f, Monad m)
             => (b -> m b') -> Cxt h f a b -> m (Cxt h f a b')
dimapMCxt f = run
              where run (In t) = liftM In $ dimapM run t
                    run (Var a)  = return $ Var a
                    run (Hole b) = liftM Hole (f b)

{-| A restricted form of |appHomM'| which only works for terms. -}
appTHomM' :: (Ditraversable g, ParamFunctor m, Monad m, Difunctor g)
             => HomM m f g -> Term f -> m (Term g)
appTHomM' f (Term t) = termM (appHomM' f t)
            

{-| This function constructs the unique monadic homomorphism from the
  initial term algebra to the given term algebra. -}
homMD :: forall f g m. (Difunctor f, Difunctor g, Monad m)
         => HomMD m f g -> CxtFunM m f g
homMD f = run 
    where run :: CxtFunM m f g
          run (In t) = liftM appCxt (f (difmap run t))
          run (Hole x) = return (Hole x)
          run (Var p) = return (Var p)

{-| This function applies a monadic signature function to the given context. -}
appSigFunM :: forall m f g. (Ditraversable f, Monad m)
              => SigFunM m f g -> CxtFunM m f g
appSigFunM f = run
    where run :: CxtFunM m f g
          run (In t) = liftM In . f =<< dimapM run t
          run (Var x) = return $ Var x
          run (Hole x) = return $ Hole x
-- implementation via term homomorphisms
--  appSigFunM f = appHomM $ hom' f

{-| A restricted form of |appSigFunM| which only works for terms. -}
appTSigFunM :: (Ditraversable f, ParamFunctor m, Monad m, Difunctor g)
               => SigFunM m f g -> Term f -> m (Term g)
appTSigFunM f (Term t) = termM (appSigFunM f t)

-- | This function applies a monadic signature function to the given
-- context. This is a 'top-down variant of 'appSigFunM'.
appSigFunM' :: forall m f g. (Ditraversable g, Monad m)
               => SigFunM m f g -> CxtFunM m f g
appSigFunM' f = run
    where run :: CxtFunM m f g
          run (In t) = liftM In . dimapM run =<< f t
          run (Var x) = return $ Var x
          run (Hole x) = return $ Hole x

{-| A restricted form of |appSigFunM'| which only works for terms. -}
appTSigFunM' :: (Ditraversable g, ParamFunctor m, Monad m, Difunctor g)
                => SigFunM m f g -> Term f -> m (Term g)
appTSigFunM' f (Term t) = termM (appSigFunM' f t)

{-| This function applies a signature function to the given context. -}
appSigFunMD :: forall f g m. (Ditraversable f, Difunctor g, Monad m)
               => SigFunMD m f g -> CxtFunM m f g
appSigFunMD f = run 
    where run :: CxtFunM m f g
          run (In t) = liftM In (f (difmap run t))
          run (Hole x) = return (Hole x)
          run (Var p) = return (Var p)

{-| A restricted form of |appSigFunMD| which only works for terms. -}
appTSigFunMD :: (Ditraversable f, ParamFunctor m, Monad m, Difunctor g)
                => SigFunMD m f g -> Term f -> m (Term g)
appTSigFunMD f (Term t) = termM (appSigFunMD f t)

{-| Compose two monadic term homomorphisms. -}
compHomM :: (Ditraversable g, Difunctor h, Monad m)
            => HomM m g h -> HomM m f g -> HomM m f h
compHomM f g = appHomM f <=< g

{-| Compose two monadic term homomorphisms. -}
compHomM' :: (Ditraversable h, Monad m) => HomM m g h -> HomM m f g -> HomM m f h
compHomM' f g = appHomM' f <=< g

{-{-| Compose two monadic term homomorphisms. -}
compHomM_ :: (Difunctor h, Difunctor g, Monad m)
                => Hom g h -> HomM m f g -> HomM m f h
compHomM_ f g = liftM (appHom f) . g

{-| Compose two monadic term homomorphisms. -}
compHomSigFunM :: Monad m => HomM m g h -> SigFunM m f g -> HomM m f h
compHomSigFunM f g = f <=< g-}

{-| Compose two monadic term homomorphisms. -}
compSigFunHomM :: (Ditraversable g, Monad m)
                  => SigFunM m g h -> HomM m f g -> HomM m f h
compSigFunHomM f g = appSigFunM f <=< g

{-| Compose two monadic term homomorphisms. -}
compSigFunHomM' :: (Ditraversable h, Monad m)
                   => SigFunM m g h -> HomM m f g -> HomM m f h
compSigFunHomM' f g = appSigFunM' f <=< g

{-| Compose a monadic algebra with a monadic term homomorphism to get a new
  monadic algebra. -}
compAlgM :: (Ditraversable g, Monad m) => AlgM m g a -> HomM m f g -> AlgM m f a
compAlgM alg talg = freeM alg return <=< talg


{-| Compose a monadic algebra with a term homomorphism to get a new monadic
  algebra. -}
compAlgM' :: (Ditraversable g, Monad m) => AlgM m g a -> Hom f g -> AlgM m f a
compAlgM' alg talg = freeM alg return . talg

{-| Compose a monadic algebra with a monadic signature function to get a new
  monadic algebra. -}
compAlgSigFunM :: Monad m => AlgM m g a -> SigFunM m f g -> AlgM m f a
compAlgSigFunM alg talg = alg <=< talg


{-| Compose a monadic algebra with a signature function to get a new monadic
  algebra. -}
compAlgSigFunM' :: AlgM m g a -> SigFun f g -> AlgM m f a
compAlgSigFunM' alg talg = alg . talg

{-| This function composes two monadic signature functions. -}
compSigFunM :: Monad m => SigFunM m g h -> SigFunM m f g -> SigFunM m f h
compSigFunM f g = f <=< g


----------------
-- Coalgebras --
----------------

{-| This type represents a coalgebra over a difunctor @f@ and carrier @a@. The
  list of @(a,b)@s represent the parameters that may occur in the constructed
  value. The first component represents the seed of the parameter,
  and the second component is the (polymorphic) parameter itself. If @f@ is
  itself a binder, then the parameters bound by @f@ can be passed to the
  covariant argument, thereby making them available to sub terms. -}
type Coalg f a = forall b. a -> [(a,b)] -> Either b (f b (a,[(a,b)]))

{-| Construct an anamorphism from the given coalgebra. -}
ana :: Difunctor f => Coalg f a -> a -> Term f
ana f x = Term $ anaAux f x
    where anaAux :: Difunctor f => Coalg f a -> a -> (forall a. Trm f a)
          anaAux f x = run (x,[])
              where run (a,bs) = case f a bs of
                                   Left p -> Var p
                                   Right t -> In $ difmap run t

{-| This type represents a monadic coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CoalgM m f a = forall b. a -> [(a,b)] -> m (Either b (f b (a,[(a,b)])))

{-| Construct a monadic anamorphism from the given monadic coalgebra. -}
anaM :: forall a m f. (Ditraversable f, Monad m)
     => CoalgM m f a -> a -> forall a. m (Trm f a)
anaM f x = run (x,[])
    where run (a,bs) = do c <- f a bs
                          case c of
                            Left p -> return $ Var p
                            Right t -> liftM In $ dimapM run t


--------------------------------
-- R-Algebras & Paramorphisms --
--------------------------------

{-| This type represents an r-algebra over a difunctor @f@ and carrier @a@. -}
type RAlg f a = f a (Trm f a, a) -> a

{-| Construct a paramorphism from the given r-algebra. -}
para :: forall f a. Difunctor f => RAlg f a -> Term f -> a
para f (Term t) = run t
    where run :: Trm f a -> a
          run (In t) = f $ difmap (\x -> (x, run x)) t
          run (Var x) = x

{-| This type represents a monadic r-algebra over a difunctor @f@ and carrier
  @a@. -}
type RAlgM m f a = f a (Trm f a, a) -> m a
{-| Construct a monadic paramorphism from the given monadic r-algebra. -}
paraM :: forall m f a. (Ditraversable f, Monad m) => RAlgM m f a -> Term f -> m a
paraM f (Term t) = run t
    where run :: Trm f a -> m a
          run (In t) = f =<< dimapM (\x -> run x >>= \y -> return (x, y)) t
          run (Var x) = return x


--------------------------------
-- R-Coalgebras & Apomorphisms --
--------------------------------

{-| This type represents an r-coalgebra over a difunctor @f@ and carrier @a@. -}
type RCoalg f a = forall b. a -> [(a,b)] -> Either b (f b (Either (Trm f b) (a,[(a,b)])))

{-| Construct an apomorphism from the given r-coalgebra. -}
apo :: Difunctor f => RCoalg f a -> a -> Term f
apo f x = Term (apoAux f x)
    where apoAux :: Difunctor f => RCoalg f a -> a -> (forall a. Trm f a)
          apoAux coa x = run (x,[])
              where -- run :: (a,[(a,b)]) -> Trm f b
                run (a,bs) = case coa a bs of
                               Left x -> Var x
                               Right t -> In $ difmap run' t
                -- run' :: Either (Trm f b) (a,[(a,b)]) -> Trm f b
                run' (Left t) = t
                run' (Right x) = run x



{-| This type represents a monadic r-coalgebra over a functor @f@ and carrier
  @a@. -}
type RCoalgM m f a = forall b. a -> [(a,b)] -> m (Either b (f b (Either (Trm f b) (a,[(a,b)]))))

{-| Construct a monadic apomorphism from the given monadic r-coalgebra. -}
apoM :: forall f m a. (Ditraversable f, Monad m)
        => RCoalgM m f a -> a -> forall a. m (Trm f a)
apoM coa x = run (x,[]) 
    where run (a,bs) = do
            res <- coa a bs
            case res of
              Left x -> return $ Var x
              Right t -> liftM In $ dimapM run' t
          run' (Left t) = return t
          run' (Right x) = run x


----------------------------------
-- CV-Algebras & Histomorphisms --
----------------------------------

{-| This type represents a cv-algebra over a difunctor @f@ and carrier @a@. -}
type CVAlg f a f' = f a (Trm f' a) -> a

-- | This function applies 'projectA' at the tip of the term.
projectTip  :: DistAnn f a f' => Trm f' a -> a
projectTip (In v) = snd $ projectA v
projectTip (Var p) = p

{-| Construct a histomorphism from the given cv-algebra. -}
histo :: forall f f' a. (Difunctor f, DistAnn f a f')
         => CVAlg f a f' -> Term f -> a
histo alg = projectTip . cata run
    where run :: Alg f (Trm f' a)
          run v = In $ injectA (alg v') v'
              where v' = dimap Var id v

{-| This type represents a monadic cv-algebra over a functor @f@ and carrier
  @a@. -}
type CVAlgM m f a f' = f a (Trm f' a) -> m a

{-| Construct a monadic histomorphism from the given monadic cv-algebra. -}
histoM :: forall f f' m a. (Ditraversable f, Monad m, DistAnn f a f')
          => CVAlgM m f a f' -> Term f -> m a
histoM alg (Term t) = liftM projectTip (run t)
    where run :: Trm f a -> m (Trm f' a)
          run (In t) = do t' <- dimapM run t
                          r <- alg t'
                          return $ In $ injectA r t'
          run (Var p) = return $ Var p


-----------------------------------
-- CV-Coalgebras & Futumorphisms --
-----------------------------------

{-| This type represents a cv-coalgebra over a difunctor @f@ and carrier @a@.
  The list of @(a,b)@s represent the parameters that may occur in the
  constructed value. The first component represents the seed of the parameter,
  and the second component is the (polymorphic) parameter itself. If @f@ is
  itself a binder, then the parameters bound by @f@ can be passed to the
  covariant argument, thereby making them available to sub terms. -}
type CVCoalg f a = forall b. a -> [(a,b)]
                 -> Either b (f b (Context f b (a,[(a,b)])))

{-| Construct a futumorphism from the given cv-coalgebra. -}
futu :: Difunctor f => CVCoalg f a -> a -> Term f
futu f x = Term (futuAux f x)
    where futuAux :: Difunctor f => CVCoalg f a -> a -> (forall a. Trm f a)
          futuAux coa x = run (x,[])
              where run (a,bs) = case coa a bs of
                                   Left p -> Var p
                                   Right t -> In $ difmap run' t
                    run' (In t) = In $ difmap run' t
                    run' (Hole x) = run x
                    run' (Var p) = Var p

{-| This type represents a monadic cv-coalgebra over a difunctor @f@ and carrier
  @a@. -}
type CVCoalgM m f a = forall b. a -> [(a,b)]
                    -> m (Either b (f b (Context f b (a,[(a,b)]))))

{-| Construct a monadic futumorphism from the given monadic cv-coalgebra. -}
futuM :: forall f a m. (Ditraversable f, Monad m) =>
         CVCoalgM m f a -> a -> forall a. m (Trm f a)
futuM coa x = run (x,[])
    where run (a,bs) = do c <- coa a bs
                          case c of 
                            Left p -> return $ Var p
                            Right t -> liftM In $ dimapM run' t
          run' (In t) = liftM In $ dimapM run' t
          run' (Hole x) = run x
          run' (Var p) = return $ Var p

{-| This type represents a generalised cv-coalgebra over a difunctor @f@ and
  carrier @a@. -}
type CVCoalg' f a = forall b. a -> [(a,b)] -> Context f b (a,[(a,b)])

{-| Construct a futumorphism from the given generalised cv-coalgebra. -}
futu' :: Difunctor f => CVCoalg' f a -> a -> Term f
futu' f x = Term (futuAux' f x)
    where futuAux' :: Difunctor f => CVCoalg' f a -> a -> (forall a. Trm f a)
          futuAux' coa x = run (x,[])
              where run (a,bs) = run' $ coa a bs
                    run' (In t) = In $ difmap run' t
                    run' (Hole x) = run x
                    run' (Var p) = Var p

{--------------------------------------------
-- functions only used for rewrite rules --
-------------------------------------------

appAlgHom :: forall f g d. Difunctor g => Alg g d -> Hom f g -> Term f -> d
{-# NOINLINE [1] appAlgHom #-}
appAlgHom alg hom (Term t) = run t where
    run :: Trm f d -> d
    run (In t) = run' $ hom t
    run (Var a) = a
    run' :: Context g d (Trm f d) -> d
    run' (In t) = alg $ fmap run' t
    run' (Var a) = a
    run' (Hole x) = run x


-- | This function applies a signature function after a term homomorphism.
appSigFunHom :: forall f g h. (Difunctor g)
                => SigFun g h -> Hom f g -> CxtFun f h
{-# NOINLINE [1] appSigFunHom #-}
appSigFunHom f g = run where
    run :: CxtFun f h
    run (In t) = run' $ g t
    run (Var a) = Var a
    run (Hole h) = Hole h
    run' :: Context g a (Cxt h' f a b) -> Cxt h' h a b
    run' (In t) = In $ f $ fmap run' t
    run' (Var a) = Var a
    run' (Hole h) = run h

appAlgHomM :: forall m g f d. Ditraversable g
              => AlgM m g d -> HomM m f g -> Term f -> m d
appAlgHomM alg hom (Term t) = run t where
    run :: Trm f d -> m d
    run (In t) = run' =<< hom t
    run (Var a) = return a
    run' :: Context g d (Trm f d) -> m d
    run' (In t) = alg =<< dimapM run' t
    run' (Var a) = return a
    run' (Hole x) = run x

appHomHomM :: forall m f g h. (Ditraversable g, Difunctor h)
              => HomM m g h -> HomM m f g -> CxtFunM m f h
appHomHomM f g = run where
--    run :: CxtFunM m f h
    run (In t) = run' =<< g t
    run (Var a) = return $ Var a
    run (Hole h) = return $ Hole h
--    run' :: Context g Any (Cxt h' f Any b) -> m (Cxt h' h Any b)
    run' (In t) = liftM appCxt $ f =<< dimapM run' t
    run' (Var a) = return $ Var a
    run' (Hole h) = run h

appSigFunHomM :: forall m f g h. Ditraversable g
                 => SigFunM m g h -> HomM m f g -> CxtFunM m f h
appSigFunHomM f g = run where
--    run :: CxtFunM m f h
    run (In t) = run' =<< g t
    run (Var a) = return $ Var a
    run (Hole h) = return $ Hole h
--    run' :: Context g Any (Cxt h' f Any b) -> m (Cxt h' h Any b)
    run' (In t) = liftM In $ f =<< dimapM run' t
    run' (Var a) = return $ Var a
    run' (Hole h) = run h


-------------------
-- rewrite rules --
-------------------

#ifndef NO_RULES
{-# RULES
  "cata/appHom" forall (a :: Alg g d) (h :: Hom f g) x.
    cata a (appHom h x) = cata (compAlg a h) x;

  "cata/appHom'" forall (a :: Alg g d) (h :: Hom f g) x.
    cata a (appHom' h x) = appAlgHom a h x;

  "cata/appSigFun" forall (a :: Alg g d) (h :: SigFun f g) x.
    cata a (appSigFun h x) = cata (compAlgSigFun a h) x;

  "cata/appSigFun'" forall (a :: Alg g d) (h :: SigFun f g) x.
    cata a (appSigFun' h x) = appAlgHom a (hom h) x;

  "cata/appSigFunHom" forall (f :: Alg f3 d) (g :: SigFun f2 f3)
                                      (h :: Hom f1 f2) x.
    cata f (appSigFunHom g h x) = appAlgHom (compAlgSigFun f g) h x;

  "appAlgHom/appHom" forall (a :: Alg h d) (f :: Hom f g) (h :: Hom g h) x.
    appAlgHom a h (appHom f x) = cata (compAlg a (compHom h f)) x;

  "appAlgHom/appHom'" forall (a :: Alg h d) (f :: Hom f g) (h :: Hom g h) x.
    appAlgHom a h (appHom' f x) = appAlgHom a (compHom h f) x;

  "appAlgHom/appSigFun" forall (a :: Alg h d) (f :: SigFun f g) (h :: Hom g h) x.
    appAlgHom a h (appSigFun f x) = cata (compAlg a (compHomSigFun h f)) x;

  "appAlgHom/appSigFun'" forall (a :: Alg h d) (f :: SigFun f g) (h :: Hom g h) x.
    appAlgHom a h (appSigFun' f x) = appAlgHom a (compHomSigFun h f) x;

  "appAlgHom/appSigFunHom" forall (a :: Alg i d) (f :: Hom f g) (g :: SigFun g h)
                                          (h :: Hom h i) x.
    appAlgHom a h (appSigFunHom g f x)
      = appAlgHom a (compHom (compHomSigFun h g) f) x;

  "appHom/appHom" forall (a :: Hom g h) (h :: Hom f g) x.
    appHom a (appHom h x) = appHom (compHom a h) x;

  "appHom'/appHom'" forall (a :: Hom g h) (h :: Hom f g) x.
    appHom' a (appHom' h x) = appHom' (compHom a h) x;

  "appHom'/appHom" forall (a :: Hom g h) (h :: Hom f g) x.
    appHom' a (appHom h x) = appHom (compHom a h) x;

  "appHom/appHom'" forall (a :: Hom g h) (h :: Hom f g) x.
    appHom a (appHom' h x) = appHom' (compHom a h) x;
    
  "appSigFun/appSigFun" forall (f :: SigFun g h) (g :: SigFun f g) x.
    appSigFun f (appSigFun g x) = appSigFun (compSigFun f g) x;

  "appSigFun'/appSigFun'" forall (f :: SigFun g h) (g :: SigFun f g) x.
    appSigFun' f (appSigFun' g x) = appSigFun' (compSigFun f g) x;

  "appSigFun/appSigFun'" forall (f :: SigFun g h) (g :: SigFun f g) x.
    appSigFun f (appSigFun' g x) = appSigFunHom f (hom g) x;

  "appSigFun'/appSigFun" forall (f :: SigFun g h) (g :: SigFun f g) x.
    appSigFun' f (appSigFun g x) = appSigFun (compSigFun f g) x;

  "appHom/appSigFun" forall (f :: Hom g h) (g :: SigFun f g) x.
    appHom f (appSigFun g x) = appHom (compHomSigFun f g) x;

  "appHom/appSigFun'" forall (f :: Hom g h) (g :: SigFun f g) x.
    appHom f (appSigFun' g x) =  appHom' (compHomSigFun f g) x;

  "appHom'/appSigFun'" forall (f :: Hom g h) (g :: SigFun f g) x.
    appHom' f (appSigFun' g x) =  appHom' (compHomSigFun f g) x;

  "appHom'/appSigFun" forall (f :: Hom g h) (g :: SigFun f g) x.
    appHom' f (appSigFun g x) = appHom (compHomSigFun f g) x;
    
  "appSigFun/appHom" forall (f :: SigFun g h) (g :: Hom f g) x.
    appSigFun f (appHom g x) = appSigFunHom f g x;

  "appSigFun'/appHom'" forall (f :: SigFun g h) (g :: Hom f g) x.
    appSigFun' f (appHom' g x) = appHom' (compSigFunHom f g) x;

  "appSigFun/appHom'" forall (f :: SigFun g h) (g :: Hom f g) x.
    appSigFun f (appHom' g x) = appSigFunHom f g x;

  "appSigFun'/appHom" forall (f :: SigFun g h) (g :: Hom f g) x.
    appSigFun' f (appHom g x) = appHom (compSigFunHom f g) x;
    
  "appSigFunHom/appSigFun" forall (f :: SigFun f3 f4) (g :: Hom f2 f3)
                                      (h :: SigFun f1 f2) x.
    appSigFunHom f g (appSigFun h x)
    = appSigFunHom f (compHomSigFun g h) x;

  "appSigFunHom/appSigFun'" forall (f :: SigFun f3 f4) (g :: Hom f2 f3)
                                      (h :: SigFun f1 f2) x.
    appSigFunHom f g (appSigFun' h x)
    = appSigFunHom f (compHomSigFun g h) x;

  "appSigFunHom/appHom" forall (f :: SigFun f3 f4) (g :: Hom f2 f3)
                                      (h :: Hom f1 f2) x.
    appSigFunHom f g (appHom h x)
    = appSigFunHom f (compHom g h) x;

  "appSigFunHom/appHom'" forall (f :: SigFun f3 f4) (g :: Hom f2 f3)
                                      (h :: Hom f1 f2) x.
    appSigFunHom f g (appHom' h x)
    = appSigFunHom f (compHom g h) x;

  "appSigFun/appSigFunHom" forall (f :: SigFun f3 f4) (g :: SigFun f2 f3)
                                      (h :: Hom f1 f2) x.
    appSigFun f (appSigFunHom g h x) = appSigFunHom (compSigFun f g) h x;

  "appSigFun'/appSigFunHom" forall (f :: SigFun f3 f4) (g :: SigFun f2 f3)
                                      (h :: Hom f1 f2) x.
    appSigFun' f (appSigFunHom g h x) = appSigFunHom (compSigFun f g) h x;

  "appHom/appSigFunHom" forall (f :: Hom f3 f4) (g :: SigFun f2 f3)
                                      (h :: Hom f1 f2) x.
    appHom f (appSigFunHom g h x) = appHom' (compHom (compHomSigFun f g) h) x;

  "appHom'/appSigFunHom" forall (f :: Hom f3 f4) (g :: SigFun f2 f3)
                                      (h :: Hom f1 f2) x.
    appHom' f (appSigFunHom g h x) = appHom' (compHom (compHomSigFun f g) h) x;

  "appSigFunHom/appSigFunHom" forall (f1 :: SigFun f4 f5) (f2 :: Hom f3 f4)
                                             (f3 :: SigFun f2 f3) (f4 :: Hom f1 f2) x.
    appSigFunHom f1 f2 (appSigFunHom f3 f4 x)
      = appSigFunHom f1 (compHom (compHomSigFun f2 f3) f4) x; #-}

{-# RULES 
  "cataM/appHomM" forall (a :: AlgM Maybe g d) (h :: HomM Maybe f g) x.
     appHomM h x >>= cataM a =  appAlgHomM a h x;

  "cataM/appHomM'" forall (a :: AlgM Maybe g d) (h :: HomM Maybe f g) x.
     appHomM' h x >>= cataM a = appAlgHomM a h x;

  "cataM/appSigFunM" forall (a :: AlgM Maybe g d) (h :: SigFunM Maybe f g) x.
     appSigFunM h x >>= cataM a = appAlgHomM a (homM h) x;

  "cataM/appSigFunM'" forall (a :: AlgM Maybe g d) (h :: SigFunM Maybe f g) x.
     appSigFunM' h x >>= cataM a = appAlgHomM a (homM h) x;

  "cataM/appHom" forall (a :: AlgM m g d) (h :: Hom f g) x.
     cataM a (appHom h x) = appAlgHomM a (sigFunM h) x;

  "cataM/appHom'" forall (a :: AlgM m g d) (h :: Hom f g) x.
     cataM a (appHom' h x) = appAlgHomM a (sigFunM h) x;

  "cataM/appSigFun" forall (a :: AlgM m g d) (h :: SigFun f g) x.
     cataM a (appSigFun h x) = appAlgHomM a (sigFunM $ hom h) x;

  "cataM/appSigFun'" forall (a :: AlgM m g d) (h :: SigFun f g) x.
     cataM a (appSigFun' h x) = appAlgHomM a (sigFunM $ hom h) x;

  "cataM/appSigFun" forall (a :: AlgM m g d) (h :: SigFun f g) x.
     cataM a (appSigFun h x) = appAlgHomM a (sigFunM $ hom h) x;

  "cataM/appSigFunHom" forall (a :: AlgM m h d) (g :: SigFun g h) (f :: Hom f g) x.
     cataM a (appSigFunHom g f x) = appAlgHomM a (sigFunM $ compSigFunHom g f) x;

  "appHomM/appHomM" forall (a :: HomM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM h x >>= appHomM a = appHomM (compHomM a h) x;

  "appHomM/appSigFunM" forall (a :: HomM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM h x >>= appHomM a = appHomM (compHomSigFunM a h) x;

  "appHomM/appHomM'" forall (a :: HomM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM' h x >>= appHomM a = appHomHomM a h x;

  "appHomM/appSigFunM'" forall (a :: HomM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM' h x >>= appHomM a = appHomHomM a (homM h) x;

  "appHomM'/appHomM" forall (a :: HomM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM h x >>= appHomM' a = appHomM' (compHomM' a h) x;

  "appHomM'/appSigFunM" forall (a :: HomM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM h x >>= appHomM' a = appHomM' (compHomSigFunM a h) x;

  "appHomM'/appHomM'" forall (a :: HomM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM' h x >>= appHomM' a = appHomM' (compHomM' a h) x;

  "appHomM'/appSigFunM'" forall (a :: HomM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM' h x >>= appHomM' a = appHomM' (compHomSigFunM a h) x;

  "appHomM/appHom" forall (a :: HomM m g h) (h :: Hom f g) x.
     appHomM a (appHom h x) = appHomHomM a (sigFunM h) x;

  "appHomM/appSigFun" forall (a :: HomM m g h) (h :: SigFun f g) x.
     appHomM a (appSigFun h x) = appHomHomM a (sigFunM $ hom h) x;

  "appHomM'/appHom" forall (a :: HomM m g h) (h :: Hom f g) x.
     appHomM' a (appHom h x) = appHomM' (compHomM' a (sigFunM h)) x;

  "appHomM'/appSigFun" forall (a :: HomM m g h) (h :: SigFun f g) x.
     appHomM' a (appSigFun h x) = appHomM' (compHomSigFunM a (sigFunM h)) x;

  "appHomM/appHom'" forall (a :: HomM m g h) (h :: Hom f g) x.
     appHomM a (appHom' h x) = appHomHomM a (sigFunM h) x;

  "appHomM/appSigFun'" forall (a :: HomM m g h) (h :: SigFun f g) x.
     appHomM a (appSigFun' h x) = appHomHomM a (sigFunM $ hom h) x;

  "appHomM'/appHom'" forall (a :: HomM m g h) (h :: Hom f g) x.
     appHomM' a (appHom' h x) = appHomM' (compHomM' a (sigFunM h)) x;

  "appHomM'/appSigFun'" forall (a :: HomM m g h) (h :: SigFun f g) x.
     appHomM' a (appSigFun' h x) = appHomM' (compHomSigFunM a (sigFunM h)) x;

  "appSigFunM/appHomM" forall (a :: SigFunM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM h x >>= appSigFunM a = appSigFunHomM a h x;

  "appSigFunHomM/appSigFunM" forall (a :: SigFunM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM h x >>= appSigFunM a = appSigFunM (compSigFunM a h) x;

  "appSigFunM/appHomM'" forall (a :: SigFunM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM' h x >>= appSigFunM a = appSigFunHomM a h x;

  "appSigFunM/appSigFunM'" forall (a :: SigFunM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM' h x >>= appSigFunM a = appSigFunHomM a (homM h) x;

  "appSigFunM'/appHomM" forall (a :: SigFunM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM h x >>= appSigFunM' a = appHomM' (compSigFunHomM' a h) x;

  "appSigFunM'/appSigFunM" forall (a :: SigFunM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM h x >>= appSigFunM' a = appSigFunM' (compSigFunM a h) x;

  "appSigFunM'/appHomM'" forall (a :: SigFunM Maybe g h) (h :: HomM Maybe f g) x.
     appHomM' h x >>= appSigFunM' a = appHomM' (compSigFunHomM' a h) x;

  "appSigFunM'/appSigFunM'" forall (a :: SigFunM Maybe g h) (h :: SigFunM Maybe f g) x.
     appSigFunM' h x >>= appSigFunM' a = appSigFunM' (compSigFunM a h) x;

  "appSigFunM/appHom" forall (a :: SigFunM m g h) (h :: Hom f g) x.
     appSigFunM a (appHom h x) = appSigFunHomM a (sigFunM h) x;

  "appSigFunM/appSigFun" forall (a :: SigFunM m g h) (h :: SigFun f g) x.
     appSigFunM a (appSigFun h x) = appSigFunHomM a (sigFunM $ hom h) x;

  "appSigFunM'/appHom" forall (a :: SigFunM m g h) (h :: Hom f g) x.
     appSigFunM' a (appHom h x) = appHomM' (compSigFunHomM' a (sigFunM h)) x;

  "appSigFunM'/appSigFun" forall (a :: SigFunM m g h) (h :: SigFun f g) x.
     appSigFunM' a (appSigFun h x) = appSigFunM' (compSigFunM a (sigFunM h)) x;

  "appSigFunM/appHom'" forall (a :: SigFunM m g h) (h :: Hom f g) x.
     appSigFunM a (appHom' h x) = appSigFunHomM a (sigFunM h) x;

  "appSigFunM/appSigFun'" forall (a :: SigFunM m g h) (h :: SigFun f g) x.
     appSigFunM a (appSigFun' h x) = appSigFunHomM a (sigFunM $ hom h) x;

  "appSigFunM'/appHom'" forall (a :: SigFunM m g h) (h :: Hom f g) x.
     appSigFunM' a (appHom' h x) = appHomM' (compSigFunHomM' a (sigFunM h)) x;

  "appSigFunM'/appSigFun'" forall (a :: SigFunM m g h) (h :: SigFun f g) x.
     appSigFunM' a (appSigFun' h x) = appSigFunM' (compSigFunM a (sigFunM h)) x;


  "appHom/appHomM" forall (a :: Hom g h) (h :: HomM m f g) x.
     appHomM h x >>= (return . appHom a) = appHomM (compHomM_ a h) x; #-}
#endif
-}
