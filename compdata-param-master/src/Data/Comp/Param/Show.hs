{-# LANGUAGE TypeOperators, FlexibleInstances, TypeSynonymInstances,
  IncoherentInstances, UndecidableInstances, TemplateHaskell, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Show
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines showing of signatures, which lifts to showing of terms.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Show
    (
     ShowD(..)
    ) where

import Data.Comp.Param.Term
import Data.Comp.Param.Ops
import Data.Comp.Param.Derive
import Data.Comp.Param.FreshM

-- Lift ShowD to sums
$(derive [liftSum] [''ShowD])

{-| From an 'ShowD' difunctor an 'ShowD' instance of the corresponding term type
  can be derived. -}
instance (Difunctor f, ShowD f) => ShowD (Cxt h f) where
    showD (In t) = showD $ fmap showD t
    showD (Hole h) = h
    showD (Var p) = return $ show p

{-| Printing of terms. -}
instance (Difunctor f, ShowD f) => Show (Term f) where
    show = evalFreshM . showD . toCxt . unTerm

instance (ShowD f, Show p) => ShowD (f :&: p) where
    showD (x :&: p) = do sx <- showD x
                         return $ sx ++ " :&: " ++ show p