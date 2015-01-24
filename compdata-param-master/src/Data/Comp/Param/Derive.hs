{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module contains functionality for automatically deriving boilerplate
-- code using Template Haskell. Examples include instances of 'Difunctor',
-- 'Difoldable', and 'Ditraversable'.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive
    (
     derive,
     -- |Derive boilerplate instances for parametric signatures, i.e.
     -- signatures for parametric compositional data types.

     -- ** EqD
     module Data.Comp.Param.Derive.Equality,
     -- ** OrdD
     module Data.Comp.Param.Derive.Ordering,
     -- ** ShowD
     module Data.Comp.Param.Derive.Show,
     -- ** Difunctor
     module Data.Comp.Param.Derive.Difunctor,
     -- ** Ditraversable
     module Data.Comp.Param.Derive.Ditraversable,
     -- ** Smart Constructors
     module Data.Comp.Param.Derive.SmartConstructors,
     -- ** Smart Constructors w/ Annotations
     module Data.Comp.Param.Derive.SmartAConstructors,
     -- ** Lifting to Sums
     liftSum
    ) where

import Data.Comp.Derive.Utils (derive, liftSumGen)
import Data.Comp.Param.Derive.Equality
import Data.Comp.Param.Derive.Ordering
import Data.Comp.Param.Derive.Show
import Data.Comp.Param.Derive.Difunctor
import Data.Comp.Param.Derive.Ditraversable
import Data.Comp.Param.Derive.SmartConstructors
import Data.Comp.Param.Derive.SmartAConstructors
import Data.Comp.Param.Ops ((:+:), caseD)

import Language.Haskell.TH

{-| Given the name of a type class, where the first parameter is a difunctor,
  lift it to sums of difunctors. Example: @class ShowD f where ...@ is lifted
  as @instance (ShowD f, ShowD g) => ShowD (f :+: g) where ... @. -}
liftSum :: Name -> Q [Dec]
liftSum = liftSumGen 'caseD ''(:+:)