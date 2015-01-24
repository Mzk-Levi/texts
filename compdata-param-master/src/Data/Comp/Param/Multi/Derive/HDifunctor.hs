{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.HDifunctor
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HDifunctor@.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Multi.Derive.HDifunctor
    (
     HDifunctor,
     makeHDifunctor
    ) where

import Data.Comp.Derive.Utils
import Data.Comp.Param.Multi.HDifunctor
import Language.Haskell.TH

{-| Derive an instance of 'HDifunctor' for a type constructor of any parametric
  kind taking at least three arguments. -}
makeHDifunctor :: Name -> Q [Dec]
makeHDifunctor fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''HDifunctor) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  hdimapDecl <- funD 'hdimap (map (hdimapClause conArg coArg) constrs')
  return [InstanceD [] classType [hdimapDecl]]
      where hdimapClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            hdimapClause conArg coArg (constr, args) = do
              fn <- newName "_f"
              gn <- newName "_g"
              varNs <- newNames (length args) "x"
              let f = varE fn
              let g = varE gn
              let fp = VarP fn
              let gp = VarP gn
              -- Pattern for the constructor
              let pat = ConP constr $ map VarP varNs
              body <- hdimapArgs conArg coArg f g (zip varNs args) (conE constr)
              return $ Clause [fp, gp, pat] (NormalB body) []
            hdimapArgs :: Name -> Name -> ExpQ -> ExpQ
                      -> [(Name, Type)] -> ExpQ -> ExpQ
            hdimapArgs _ _ _ _ [] acc =
                acc
            hdimapArgs conArg coArg f g ((x,tp):tps) acc =
                hdimapArgs conArg coArg f g tps
                          (acc `appE` (hdimapArg conArg coArg tp f g `appE` varE x))
            hdimapArg :: Name -> Name -> Type -> ExpQ -> ExpQ -> ExpQ
            hdimapArg conArg coArg tp f g
                | not (containsType tp (VarT conArg)) &&
                  not (containsType tp (VarT coArg)) = [| id |]
                | otherwise =
                    case tp of
                      AppT (VarT a) _ | a == conArg -> f
                                      | a == coArg -> g
                      AppT (AppT ArrowT tp1) tp2 -> do
                          xn <- newName "x"
                          let ftp1 = hdimapArg conArg coArg tp1 f g
                          let ftp2 = hdimapArg conArg coArg tp2 f g
                          lamE [varP xn]
                               (infixE (Just ftp2)
                                       [|(.)|]
                                       (Just $ infixE (Just $ varE xn)
                                                      [|(.)|]
                                                      (Just ftp1)))
                      SigT tp' _ ->
                          hdimapArg conArg coArg tp' f g
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| hdimap $f $g |]
                          else
                              [| fmap $g |]
