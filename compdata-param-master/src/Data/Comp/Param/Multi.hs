--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>, Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Generalised Parametric Compositional Data Types/. Generalised Parametric
-- Compositional Data Types is an extension of Compositional Data Types with
-- parametric higher-order abstract syntax (PHOAS) for usage with binders, and
-- GADTs. Generalised Parametric Compositional Data Types combines Generalised
-- Compositional Data Types ("Data.Comp.Multi") and Parametric Compositional
-- Data Types ("Data.Comp.Param"). Examples of usage are bundled with the
-- package in the library @examples\/Examples\/Param.Multi@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi (
    module Data.Comp.Param.Multi.Term
  , module Data.Comp.Param.Multi.Algebra
  , module Data.Comp.Param.Multi.HDifunctor
  , module Data.Comp.Param.Multi.Sum
  , module Data.Comp.Param.Multi.Annotation
  , module Data.Comp.Param.Multi.Equality
    ) where

import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.Algebra
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.Sum
import Data.Comp.Param.Multi.Annotation
import Data.Comp.Param.Multi.Equality
