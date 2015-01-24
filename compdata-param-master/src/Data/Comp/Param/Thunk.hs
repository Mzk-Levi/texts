{-# LANGUAGE TypeOperators, FlexibleContexts, Rank2Types, GADTs #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Thunk
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines terms & contexts with thunks, with deferred
-- monadic computations.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Thunk
    (TermT
    ,TrmT
    ,CxtT
    ,Thunk
    ,thunk
    ,whnf
    ,whnf'
    ,whnfPr
    ,nf
    ,nfT
    ,nfPr
    ,nfTPr
    ,evalStrict
    ,AlgT
    ,strict
    ,strict')
 where

import Data.Comp.Param.Term
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops
import Data.Comp.Param.Algebra
import Data.Comp.Param.Ditraversable
import Data.Comp.Param.Difunctor

import Control.Monad

-- | This type represents terms with thunks.
type TermT m f = Term (Thunk m :+: f)

-- | This type represents terms with thunks.
type TrmT m f a = Trm  (Thunk m :+: f) a

-- | This type represents contexts with thunks.
type CxtT h  m f a = Cxt h (Thunk m :+: f) a

newtype Thunk m a b = Thunk (m b)

-- | This function turns a monadic computation into a thunk.
thunk :: (Thunk m :<: f) => m (Cxt h f a b) -> Cxt h f a b
thunk = inject . Thunk

-- | This function evaluates all thunks until a non-thunk node is
-- found.
whnf :: Monad m => TrmT m f a -> m (Either a (f a (TrmT m f a)))
whnf (In (Inl (Thunk m))) = m >>= whnf
whnf (In (Inr t)) = return $ Right t
whnf (Var x) = return $ Left x

whnf' :: Monad m => TrmT m f a -> m (TrmT m f a)
whnf' =  liftM (either Var inject) . whnf

-- | This function first evaluates the argument term into whnf via
-- 'whnf' and then projects the top-level signature to the desired
-- subsignature. Failure to do the projection is signalled as a
-- failure in the monad.
whnfPr :: (Monad m, g :<: f) => TrmT m f a -> m (g a (TrmT m f a))
whnfPr t = do res <- whnf t
              case res of
                Left _  -> fail "cannot project variable"
                Right t ->
                    case proj t of
                      Just res' -> return res'
                      Nothing -> fail "projection failed"


-- | This function evaluates all thunks.
nfT :: (ParamFunctor m, Monad m, Ditraversable f) => TermT m f -> m (Term f)
nfT t = termM $ nf $ unTerm  t

-- | This function evaluates all thunks.
nf :: (Monad m, Ditraversable f) => TrmT m f a -> m (Trm f a)
nf = either (return . Var) (liftM In . dimapM nf) <=< whnf

-- | This function evaluates all thunks while simultaneously
-- projecting the term to a smaller signature. Failure to do the
-- projection is signalled as a failure in the monad as in 'whnfPr'.
nfTPr :: (ParamFunctor m, Monad m, Ditraversable g, g :<: f) => TermT m f -> m (Term g)
nfTPr t = termM $ nfPr $ unTerm t

-- | This function evaluates all thunks while simultaneously
-- projecting the term to a smaller signature. Failure to do the
-- projection is signalled as a failure in the monad as in 'whnfPr'.
nfPr :: (Monad m, Ditraversable g, g :<: f) => TrmT m f a -> m (Trm g a)
nfPr = liftM In . dimapM nfPr <=< whnfPr


evalStrict :: (Ditraversable g, Monad m, g :<: f) => 
              (g (TrmT m f a) (f a (TrmT m f a)) -> TrmT m f a)
           -> g (TrmT m f a) (TrmT m f a) -> TrmT m f a
evalStrict cont t = thunk $ do 
                      t' <- dimapM (liftM (either (const Nothing) Just) . whnf) t
                      case disequence t' of
                        Nothing -> return $ inject' t
                        Just s -> return $ cont s
                      

-- | This type represents algebras which have terms with thunks as
-- carrier.
type AlgT m f g = Alg f (TermT m g)

-- | This combinator makes the evaluation of the given functor
-- application strict by evaluating all thunks of immediate subterms.
strict :: (f :<: g, Ditraversable f, Monad m) => f a (TrmT m g a) -> TrmT m g a
strict x = thunk $ liftM inject $ dimapM whnf' x

-- | This combinator makes the evaluation of the given functor
-- application strict by evaluating all thunks of immediate subterms.
strict' :: (f :<: g, Ditraversable f, Monad m) => f (TrmT m g a) (TrmT m g a) -> TrmT m g a
strict'  = strict . dimap Var id