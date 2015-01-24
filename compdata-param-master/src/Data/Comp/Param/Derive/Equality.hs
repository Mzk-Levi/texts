{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Equality
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @EqD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Derive.Equality
    (
     EqD(..),
     makeEqD
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.FreshM hiding (Name)
import Data.Comp.Param.Equality
import Control.Monad
import Language.Haskell.TH hiding (Cxt, match)

{-| Derive an instance of 'EqD' for a type constructor of any parametric
  kind taking at least two arguments. -}
makeEqD :: Name -> Q [Dec]
makeEqD fname = do
  -- Comments below apply to the example where name = T, args = [a,b,c], and
  -- constrs = [(X,[c]), (Y,[a,c]), (Z,[b -> c])], i.e. the data type
  -- declaration: T a b c = X c | Y a c | Z (b -> c)
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  -- coArg = c (covariant difunctor argument)
  let coArg :: Name = tyVarBndrName $ last args
  -- conArg = b (contravariant difunctor argument)
  let conArg :: Name = tyVarBndrName $ last $ init args
  -- argNames = [a]
  let argNames = map (VarT . tyVarBndrName) (init $ init args)
  -- compType = T a
  let complType = foldl AppT (ConT name) argNames
  -- classType = Difunctor (T a)
  let classType = AppT (ConT ''EqD) complType
  -- constrs' = [(X,[c]), (Y,[a,c]), (Z,[b -> c])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  let defC = if length constrs < 2 then
                 []
             else
                 [clause [wildP,wildP] (normalB [|return False|]) []]
  eqDDecl <- funD 'eqD (map (eqDClause conArg coArg) constrs' ++ defC)
  let context = map (\arg -> ClassP ''Eq [arg]) argNames
  return [InstanceD context classType [eqDDecl]]
      where eqDClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            eqDClause conArg coArg (constr, args) = do
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              -- Patterns for the constructors
              let patx = ConP constr $ map VarP varXs
              let paty = ConP constr $ map VarP varYs
              body <- eqDBody conArg coArg (zip3 varXs varYs args)
              return $ Clause [patx,paty] (NormalB body) []
            eqDBody :: Name -> Name -> [(Name, Name, Type)] -> ExpQ
            eqDBody conArg coArg x =
                [|liftM and (sequence $(listE $ map (eqDB conArg coArg) x))|]
            eqDB :: Name -> Name -> (Name, Name, Type) -> ExpQ
            eqDB conArg coArg (x, y, tp)
                | not (containsType tp (VarT conArg)) &&
                  not (containsType tp (VarT coArg)) =
                    [| return $ $(varE x) == $(varE y) |]
                | otherwise =
                    case tp of
                      VarT a
                          | a == coArg -> [| peq $(varE x) $(varE y) |]
                      AppT (AppT ArrowT (VarT a)) _
                          | a == conArg ->
                              [| withName (\v -> peq ($(varE x) v) ($(varE y) v)) |]
                      SigT tp' _ ->
                          eqDB conArg coArg (x, y, tp')
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| eqD $(varE x) $(varE y) |]
                          else
                              [| peq $(varE x) $(varE y) |]