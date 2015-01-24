{-# LANGUAGE TemplateHaskell, GADTs #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Projections
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Derive functions for signature projections.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.Projections
    (
     projn,
     projectn,
     deepProjectn
    ) where

import Language.Haskell.TH hiding (Cxt)
import Control.Monad (liftM)
import Data.Comp.Param.Ditraversable (Ditraversable)
import Data.Comp.Param.Term
import Data.Comp.Param.Algebra (appTSigFunM')
import Data.Comp.Param.Ops ((:+:)(..), (:<:)(..))

projn :: Int -> Q [Dec]
projn n = do
  let p = mkName $ "proj" ++ show n
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let avar = mkName "a"
  let bvar = mkName "b"
  let xvar = mkName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar gvars avar bvar) []]]
  sequence $ (sigD p $ genSig gvars avar bvar) : d
    where genSig gvars avar bvar = do
            let fvar = mkName "f"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let tp' = arrowT `appT` (varT fvar `appT` varT avar `appT`
                                     varT bvar)
                             `appT` (conT ''Maybe `appT`
                                     (tp `appT` varT avar `appT` varT bvar))
            forallT (map PlainTV $ fvar : avar : bvar : gvars)
                    (sequence cxt) tp'
          genDecl x [g] a b =
            [| liftM inj (proj $(varE x)
                          :: Maybe ($(varT g `appT` varT a `appT` varT b))) |]
          genDecl x (g:gs) a b =
            [| case (proj $(varE x)
                         :: Maybe ($(varT g `appT` varT a `appT` varT b))) of
                 Just y -> Just $ inj y
                 _ -> $(genDecl x gs a b) |]
          genDecl _ _ _ _ = error "genDecl called with empty list"

projectn :: Int -> Q [Dec]
projectn n = do
  let p = mkName ("project" ++ show n)
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let avar = mkName "a"
  let bvar = mkName "b"
  let xvar = mkName "x"
  let d = [funD p [clause [varP xvar] (normalB $ genDecl xvar n) []]]
  sequence $ (sigD p $ genSig gvars avar bvar) : d
    where genSig gvars avar bvar = do
            let fvar = mkName "f"
            let hvar = mkName "h"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let tp' = conT ''Cxt `appT` varT hvar `appT` varT fvar
                                 `appT` varT avar `appT` varT bvar
            let tp'' = arrowT `appT` tp'
                              `appT` (conT ''Maybe `appT`
                                      (tp `appT` varT avar `appT` tp'))
            forallT (map PlainTV $ hvar : fvar : avar : bvar : gvars)
                    (sequence cxt) tp''
          genDecl x n = [| case $(varE x) of
                             Hole _ -> Nothing
                             Var _ -> Nothing
                             In t -> $(varE $ mkName $ "proj" ++ show n) t |]

deepProjectn :: Int -> Q [Dec]
deepProjectn n = do
  let p = mkName ("deepProject" ++ show n)
  let gvars = map (\n -> mkName $ 'g' : show n) [1..n]
  let d = [funD p [clause [] (normalB $ genDecl n) []]]
  sequence $ (sigD p $ genSig gvars) : d
    where genSig gvars = do
            let fvar = mkName "f"
            let cxt = map (\g -> classP ''(:<:) [varT g, varT fvar]) gvars
            let tp = foldl1 (\a g -> conT ''(:+:) `appT` g `appT` a)
                            (map varT gvars)
            let cxt' = classP ''Ditraversable [tp]
            let tp' = arrowT `appT` (conT ''Term `appT` varT fvar)
                             `appT` (conT ''Maybe `appT` (conT ''Term `appT` tp))
            forallT (map PlainTV $ fvar : gvars) (sequence $ cxt' : cxt) tp'
          genDecl n = [| appTSigFunM' $(varE $ mkName $ "proj" ++ show n) |]