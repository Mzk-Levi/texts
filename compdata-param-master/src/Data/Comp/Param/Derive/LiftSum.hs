{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for difunctors to sums of difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.LiftSum
    (
     liftSum,
     caseD
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Param.Sum
import Data.Comp.Param.Ops ((:+:)(..))

{-| Given the name of a type class, where the first parameter is a difunctor,
  lift it to sums of difunctors. Example: @class ShowD f where ...@ is lifted
  as @instance (ShowD f, ShowD g) => ShowD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseD ''(:+:)

{-| Utility function to case on a difunctor sum, without exposing the internal
  representation of sums. -}
caseD :: (f a b -> c) -> (g a b -> c) -> (f :+: g) a b -> c
caseD f g x = case x of
                Inl x -> f x
                Inr x -> g x