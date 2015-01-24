{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'HDifunctor',
-- 'ShowHD', and 'EqHD'.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Derive
    (
     derive,
     -- |Derive boilerplate instances for parametric signatures, i.e.
     -- signatures for parametric compositional data types.

     -- ** EqHD
     module Data.Comp.Param.Multi.Derive.Equality,
     -- ** OrdHD
     module Data.Comp.Param.Multi.Derive.Ordering,
     -- ** ShowHD
     module Data.Comp.Param.Multi.Derive.Show,
     -- ** HDifunctor
     module Data.Comp.Param.Multi.Derive.HDifunctor,
     -- ** Smart Constructors
     module Data.Comp.Param.Multi.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.Param.Multi.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     liftSum
    ) where

import Data.Comp.Derive.Utils (derive, liftSumGen)
import Data.Comp.Param.Multi.Derive.Equality
import Data.Comp.Param.Multi.Derive.Ordering
import Data.Comp.Param.Multi.Derive.Show
import Data.Comp.Param.Multi.Derive.HDifunctor
import Data.Comp.Param.Multi.Derive.SmartConstructors
import Data.Comp.Param.Multi.Derive.SmartAConstructors
import Data.Comp.Param.Multi.Ops ((:+:), caseHD)

import Language.Haskell.TH

{-| Given the name of a type class, where the first parameter is a higher-order
  difunctor, lift it to sums of higher-order difunctors. Example:
  @class ShowHD f where ...@ is lifted as
  @instance (ShowHD f, ShowHD g) => ShowHD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseHD ''(:+:)
