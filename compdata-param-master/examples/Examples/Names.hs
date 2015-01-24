{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Names
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- From names to parametric higher-order abstract syntax and back
--
-- The example illustrates how to convert a parse tree with explicit names into
-- an AST that uses parametric higher-order abstract syntax, and back again. The
-- example shows how we can easily convert object language binders to Haskell
-- binders, without having to worry about capture avoidance.
--
--------------------------------------------------------------------------------

module Examples.Names where

import Data.Comp.Param hiding (Var)
import qualified Data.Comp.Param as P
import Data.Comp.Param.Derive
import Data.Comp.Param.Ditraversable
import Data.Comp.Param.Show ()
import Data.Maybe
import qualified Data.Map as Map
import Control.Monad.Reader

data Lam a b  = Lam (a -> b)
data App a b  = App b b
data Lit a b  = Lit Int
data Plus a b = Plus b b
type Name     = String                 -- The type of names
data NLam a b = NLam Name b
data NVar a b = NVar Name
type SigB     = App :+: Lit :+: Plus
type SigN     = NLam :+: NVar :+: SigB -- The name signature
type SigP     = Lam :+: SigB           -- The PHOAS signature

$(derive [makeDifunctor, makeShowD, makeEqD, smartConstructors]
         [''Lam, ''App, ''Lit, ''Plus, ''NLam, ''NVar])
$(derive [makeDitraversable]
         [''App, ''Lit, ''Plus, ''NLam, ''NVar])

--------------------------------------------------------------------------------
-- Names to PHOAS translation
--------------------------------------------------------------------------------

type M f a = Reader (Map.Map Name (Trm f a))

class N2PTrans f g where
  n2pAlg :: Alg f (M g a (Trm g a))


-- We make the lifting to sums explicit in order to make the N2PTrans
-- work with the default instance declaration further below.
instance (N2PTrans f1 g, N2PTrans f2 g) => N2PTrans (f1 :+: f2) g where
    n2pAlg = caseD n2pAlg n2pAlg

n2p :: (Difunctor f, N2PTrans f g) => Term f -> Term g
n2p t = Term $ runReader (cata n2pAlg t) Map.empty

instance (Lam :<: g) => N2PTrans NLam g where
  n2pAlg (NLam x b) = do vars <- ask
                         return $ iLam $ \y -> runReader b (Map.insert x y vars)

instance (Ditraversable f, f :<: g) => N2PTrans f g where
  n2pAlg = liftM inject . disequence . dimap (return . P.Var) id -- default

instance N2PTrans NVar g where
  n2pAlg (NVar x) = liftM fromJust (asks (Map.lookup x))

en :: Term SigN
en = Term $ iNLam "x1" $ iNLam "x2" (iNLam "x3" $ iNVar "x2") `iApp` iNVar "x1"

ep :: Term SigP
ep = n2p en

--------------------------------------------------------------------------------
-- PHOAS to names translation
--------------------------------------------------------------------------------

type M' = Reader [Name]

class P2NTrans f g where
  p2nAlg :: Alg f (M' (Trm g a))


-- We make the lifting to sums explicit in order to make the P2NTrans
-- work with the default instance declaration further below.
instance (P2NTrans f1 g, P2NTrans f2 g) => P2NTrans (f1 :+: f2) g where
    p2nAlg = caseD p2nAlg p2nAlg


p2n :: (Difunctor f, P2NTrans f g) => Term f -> Term g
p2n t = Term $ runReader (cata p2nAlg t) ['x' : show n | n <- [1..]]

instance (Ditraversable f, f :<: g) => P2NTrans f g where
  p2nAlg = liftM inject . disequence . dimap (return . P.Var) id -- default

instance (NLam :<: g, NVar :<: g) => P2NTrans Lam g where
  p2nAlg (Lam f) = do n:names <- ask
                      return $ iNLam n (runReader (f (return $ iNVar n)) names)

ep' :: Term SigP
ep' = Term $ iLam $ \a -> iLam (\b -> (iLam $ \_ -> b)) `iApp` a

en' :: Term SigN
en' = p2n ep'
