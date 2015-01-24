{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.Equality
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @EqHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi.Derive.Equality
    (
     EqHD(..),
     makeEqHD
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.Multi.FreshM hiding (Name)
import Data.Comp.Param.Multi.Equality
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)

{-| Derive an instance of 'EqHD' for a type constructor of any parametric
  kind taking at least three arguments. -}
makeEqHD :: Name -> Q [Dec]
makeEqHD fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''EqHD) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  let defC = if length constrs < 2 then
                 []
             else
                 [clause [wildP,wildP] (normalB [|return False|]) []]
  eqHDDecl <- funD 'eqHD (map (eqHDClause conArg coArg) constrs' ++ defC)
  let context = map (\arg -> ClassP ''Eq [arg]) argNames
  return [InstanceD context classType [eqHDDecl]]
      where eqHDClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            eqHDClause conArg coArg (constr, args) = do
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              -- Patterns for the constructors
              let patx = ConP constr $ map VarP varXs
              let paty = ConP constr $ map VarP varYs
              body <- eqHDBody conArg coArg (zip3 varXs varYs args)
              return $ Clause [patx,paty] (NormalB body) []
            eqHDBody :: Name -> Name -> [(Name, Name, Type)] -> ExpQ
            eqHDBody conArg coArg x =
                [|liftM and (sequence $(listE $ map (eqHDB conArg coArg) x))|]
            eqHDB :: Name -> Name -> (Name, Name, Type) -> ExpQ
            eqHDB conArg coArg (x, y, tp)
                | not (containsType tp (VarT conArg)) &&
                  not (containsType tp (VarT coArg)) =
                    [| return $ $(varE x) == $(varE y) |]
                | otherwise =
                    case tp of
                      AppT (VarT a) _ 
                          | a == coArg -> [| peq $(varE x) $(varE y) |]
                      AppT (AppT ArrowT (AppT (VarT a) _)) _
                          | a == conArg ->
                              [| withName (\v -> peq ($(varE x) $ nameCoerce v)                                                      ($(varE y) $ nameCoerce v)) |]
                      SigT tp' _ ->
                          eqHDB conArg coArg (x, y, tp')
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| eqHD $(varE x) $(varE y) |]
                          else
                              [| peq $(varE x) $(varE y) |]
