--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>, Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines the infrastructure necessary to use
-- /Parametric Compositional Data Types/. Parametric Compositional Data Types 
-- is an extension of Compositional Data Types with parametric
-- higher-order abstract syntax (PHOAS) for usage with binders. Examples of
-- usage are bundled with the package in the library
-- @examples\/Examples\/Param@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param (
    module Data.Comp.Param.Term
  , module Data.Comp.Param.Algebra
  , module Data.Comp.Param.Difunctor
  , module Data.Comp.Param.Sum
  , module Data.Comp.Param.Annotation
  , module Data.Comp.Param.Equality
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Algebra
import Data.Comp.Param.Difunctor
import Data.Comp.Param.Sum
import Data.Comp.Param.Annotation
import Data.Comp.Param.Equality