{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.Injections
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Derive functions for signature injections.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Derive.Injections
    (
     injn,
     injectn,
     deepInjectn
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Param.Multi.HDifunctor
import Data.Comp.Param.Multi.Term
import Data.Comp.Param.Multi.Algebra (CxtFun, appSigFun)
import Data.Comp.Param.Multi.Ops ((:+:)(..), (:<:)(..))

injn :: Int -> Q [Dec]
injn n = do
  let i = mkName $ "inj" ++ show n
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let avar = mkName "a"
  let bvar = mkName "b"
  let ivar = mkName "i"
  let xvar = mkName "x"
  let d = [funD i [clause [varP xvar] (normalB $ genDecl xvar n) []]]
  sequence $ sigD i (genSig fvars gvar avar bvar ivar) : d
    where genSig fvars gvar avar bvar ivar = do
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let tp' = arrowT `appT` (tp `appT` varT avar `appT`
                                     varT bvar `appT` varT ivar)
                             `appT` (varT gvar `appT` varT avar `appT`
                                     varT bvar `appT` varT ivar)
            forallT (map PlainTV $ gvar : avar : bvar : ivar : fvars)
                    (sequence cxt) tp'
          genDecl x n = [| case $(varE x) of
                             Inl x -> $(varE $ mkName "inj") x
                             Inr x -> $(varE $ mkName $ "inj" ++
                                        if n > 2 then show (n - 1) else "") x |]
injectn :: Int -> Q [Dec]
injectn n = do
  let i = mkName ("inject" ++ show n)
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let avar = mkName "a"
  let bvar = mkName "b"
  let ivar = mkName "i"
  let d = [funD i [clause [] (normalB $ genDecl n) []]]
  sequence $ sigD i (genSig fvars gvar avar bvar ivar) : d
    where genSig fvars gvar avar bvar ivar = do
            let hvar = mkName "h"
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let tp' = conT ''Cxt `appT` varT hvar `appT` varT gvar
                                 `appT` varT avar `appT` varT bvar
            let tp'' = arrowT `appT` (tp `appT` varT avar `appT`
                                      tp' `appT` varT ivar)
                              `appT` (tp' `appT` varT ivar)
            forallT (map PlainTV $ hvar : gvar : avar : bvar : ivar : fvars)
                    (sequence cxt) tp''
          genDecl n = [| In . $(varE $ mkName $ "inj" ++ show n) |]

deepInjectn :: Int -> Q [Dec]
deepInjectn n = do
  let i = mkName ("deepInject" ++ show n)
  let fvars = map (\n -> mkName $ 'f' : show n) [1..n]
  let gvar = mkName "g"
  let d = [funD i [clause [] (normalB $ genDecl n) []]]
  sequence $ sigD i (genSig fvars gvar) : d
    where genSig fvars gvar = do
            let cxt = map (\f -> classP ''(:<:) [varT f, varT gvar]) fvars
            let tp = foldl1 (\a f -> conT ''(:+:) `appT` f `appT` a)
                            (map varT fvars)
            let cxt' = classP ''HDifunctor [tp]
            let tp' = conT ''CxtFun `appT` tp `appT` varT gvar
            forallT (map PlainTV $ gvar : fvars) (sequence $ cxt' : cxt) tp'
          genDecl n = [| appSigFun $(varE $ mkName $ "inj" ++ show n) |]
