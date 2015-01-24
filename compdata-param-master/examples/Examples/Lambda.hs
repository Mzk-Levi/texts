{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  OverlappingInstances, Rank2Types, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Lambda
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lambda calculus examples
--
-- We define a pretty printer, a desugaring transformation, constant folding,
-- and call-by-value interpreter for an extended variant of the simply typed
-- lambda calculus.
--
--------------------------------------------------------------------------------

module Examples.Lambda where

import Data.Comp.Param
import Data.Comp.Param.Show ()
import Data.Comp.Param.Equality ()
import Data.Comp.Param.Ordering ()
import Data.Comp.Param.Derive
import Data.Comp.Param.Desugar

data Lam a b   = Lam (a -> b)
data App a b   = App b b
data Const a b = Const Int
data Plus a b  = Plus b b
data Let a b   = Let b (a -> b)
data Err a b   = Err

type Sig       = Lam :+: App :+: Const :+: Plus :+: Let :+: Err
type Sig'      = Lam :+: App :+: Const :+: Plus :+: Err

$(derive [smartConstructors, makeDifunctor, makeShowD, makeEqD, makeOrdD]
         [''Lam, ''App, ''Const, ''Plus, ''Let, ''Err])

-- * Pretty printing
data Stream a = Cons a (Stream a)

class Pretty f where
  prettyAlg :: Alg f (Stream String -> String)

$(derive [liftSum] [''Pretty])

pretty :: (Difunctor f, Pretty f) => Term f -> String
pretty t = cata prettyAlg t (nominals 1)
    where nominals n = Cons ('x' : show n) (nominals (n + 1))

instance Pretty Lam where
  prettyAlg (Lam f) (Cons x xs) = "(\\" ++ x ++ ". " ++ f (const x) xs ++ ")"

instance Pretty App where
  prettyAlg (App e1 e2) xs = "(" ++ e1 xs ++ " " ++ e2 xs ++ ")"

instance Pretty Const where
  prettyAlg (Const n) _ = show n

instance Pretty Plus where
  prettyAlg (Plus e1 e2) xs = "(" ++ e1 xs ++ " + " ++ e2 xs ++ ")"

instance Pretty Err where
  prettyAlg Err _ = "error"

instance Pretty Let where
  prettyAlg (Let e1 e2) (Cons x xs) = "let " ++ x ++ " = " ++ e1 xs ++ " in " ++ e2 (const x) xs

-- * Desugaring
instance (Difunctor f, App :<: f, Lam :<: f) => Desugar Let f where
  desugHom' (Let e1 e2) = inject (Lam e2) `iApp` e1

-- * Constant folding
class Constf f g where
  constfAlg :: forall a. Alg f (Trm g a)

$(derive [liftSum] [''Constf])

constf :: (Difunctor f, Constf f g) => Term f -> Term g
constf t = Term (cata constfAlg t)

instance (Difunctor f, f :<: g) => Constf f g where
  constfAlg = inject . dimap Var id -- default instance

instance (Plus :<: f, Const :<: f) => Constf Plus f where
  constfAlg (Plus e1 e2) = case (project e1, project e2) of
                             (Just (Const n),Just (Const m)) -> iConst (n + m)
                             _                               -> e1 `iPlus` e2

-- * Call-by-value evaluation
data Sem m = Fun (Sem m -> m (Sem m)) | Int Int

class Monad m => Eval f m where
  evalAlg :: Alg f (m (Sem m))

$(derive [liftSum] [''Eval])

eval :: (Difunctor f, Eval f m) => Term f -> m (Sem m)
eval = cata evalAlg

instance Monad m => Eval Lam m where
  evalAlg (Lam f) = return (Fun (f . return))

instance Monad m => Eval App m where
  evalAlg (App mx my) = do x <- mx
                           case x of Fun f -> f =<< my; _ -> fail "stuck"

instance Monad m => Eval Const m where
  evalAlg (Const n) = return (Int n)

instance Monad m => Eval Plus m where
  evalAlg (Plus mx my) = do x <- mx
                            y <- my
                            case (x,y) of (Int n,Int m) -> return (Int (n + m))
                                          _             -> fail "stuck"

instance Monad m => Eval Err m where
  evalAlg Err = fail "error"

e :: Term Sig
e = Term (iLet (iConst 2) (\x -> (iLam (\y -> y `iPlus` x) `iApp` iConst 3)))

e' :: Term Sig'
e' = desugar e

evalEx :: Maybe (Sem Maybe)
evalEx = eval e'
