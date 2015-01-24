{-# LANGUAGE TemplateHaskell, TypeOperators, MultiParamTypeClasses,
  FlexibleInstances, FlexibleContexts, UndecidableInstances, OverlappingInstances #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.Param.Thunk
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
--------------------------------------------------------------------------------

module Examples.Thunk where

import Data.Comp.Param
import Data.Comp.Param.Show ()
import Data.Comp.Param.Derive
import Data.Comp.Param.Thunk

-- Signatures for values and operators
data Const a e = Const Int
data Lam a e = Lam (a -> e) -- Note: not e -> e
data App a e = App e e
data Op a e = Add e e | Mult e e
data Fun a e = Fun (e -> e) -- Note: not a -> e

-- Signature for the simple expression language
type Sig = Const :+: Lam :+: App :+: Op
-- Signature for values. Note the use of 'FunM' rather than 'Lam' (!)
type Value = Const :+: Fun
-- Signature for ground values.
type GValue = Const

-- Derive boilerplate code using Template Haskell
$(derive [makeDifunctor, makeEqD, makeOrdD, makeShowD, smartConstructors]
         [''Const, ''Lam, ''App, ''Op])
$(derive [makeDitraversable]
         [''Const, ''App, ''Op])

-- Term evaluation algebra. Note that we cannot use @AlgM Maybe f (Term v)@
-- because that would force @FunM@ to have the type @e -> e@ rather than
-- @e -> m e@. The latter is needed because the input to a @Lam@ (which is
-- evaluated to a @Fun@) will determine whether or not an error should be
-- returned. Example: @(\x -> x x) 42@ will produce an error because the
-- abstraction is applied to a non-functional, whereas @(\x -> x x)(\y -> y)@
-- will not.
class EvalT f v where
  evalAlgT :: Alg f (TrmT Maybe v a)

$(derive [liftSum] [''EvalT])

-- Lift the evaluation algebra to a catamorphism
evalT :: (Difunctor f, Ditraversable v, EvalT f v) => Term f -> Maybe (Term v)
evalT t = nfT $ Term (cata evalAlgT t)

-- instance (Ditraversable f Maybe Any, f :<: v) => EvalT f v where
--   evalAlgT  = strict'

instance (Difunctor f, f :<: v) => EvalT f v where
  evalAlgT  = inject'


instance (Const :<: v) => EvalT Op v where
  evalAlgT (Add mx my)  = thunk $ do 
                            Const x <- whnfPr mx
                            Const y <- whnfPr my
                            return $ iConst $ x + y
  evalAlgT (Mult mx my) = thunk $ do 
                            Const x <- whnfPr mx
                            Const y <- whnfPr my
                            return $ iConst $ x * y

instance (Fun :<: v) => EvalT App v where
  evalAlgT (App mx my) = thunk $ do 
                           Fun f <- whnfPr mx
                           -- lazy
                           return $ f my
                           -- strict
                           -- liftM f $ whnf' my

instance (Fun :<: v) => EvalT Lam v where
  evalAlgT (Lam f) = inject $ Fun f

-- |Evaluation of expressions to ground values.
evalMG :: Term Sig -> Maybe (Term GValue)
evalMG e = termM $ nfPr $ eval e
  where eval :: Term Sig -> TrmT Maybe Value a
        eval = cata evalAlgT


-- Example: evalEx = Just (iConst 12) (3 * (2 + 2) = 12)
evalMEx :: Maybe (Term GValue)
evalMEx = evalMG $ Term $ iLam (\x -> iLam $ \y -> y `iMult` (x `iAdd` x))
                   `iApp` iConst 2 `iApp` iConst 3

-- Example: type error
evalMEx' :: Maybe (Term GValue)
evalMEx' = evalMG $ Term $ iLam (\x -> iLam $ \y -> x `iMult` (x `iAdd` x))
                   `iApp` iConst 2 `iApp` (iLam (\x -> x) `iAdd` iConst 2)

-- Example: non-termination
evalMExY :: Maybe (Term GValue)
evalMExY = evalMG $ Term $ iLam (\x -> iLam $ \y -> x `iMult` (x `iAdd` x))
                   `iApp` iConst 2 `iApp` omega
    where omega = iLam (\x -> x `iApp` x) `iApp` iLam (\x -> x `iApp` x)
