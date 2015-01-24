{-# LANGUAGE TemplateHaskell, TypeOperators #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.LiftSum
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Lift a class declaration for higher-order difunctors to sums of higher-order
-- difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Derive.LiftSum
    (
     liftSum,
     caseHD
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Param.Multi.Sum
import Data.Comp.Param.Multi.Ops ((:+:)(..))

{-| Given the name of a type class, where the first parameter is a higher-order
  difunctor, lift it to sums of higher-order difunctors. Example:
  @class ShowHD f where ...@ is lifted as
  @instance (ShowHD f, ShowHD g) => ShowHD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseHD ''(:+:)

{-| Utility function to case on a higher-order difunctor sum, without exposing
  the internal representation of sums. -}
caseHD :: (f a b i -> c) -> (g a b i -> c) -> (f :+: g) a b i -> c
caseHD f g x = case x of
                 Inl x -> f x
                 Inr x -> g x
