{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Multi.Derive.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @OrdHD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Multi.Derive.Ordering
    (
     OrdHD(..),
     makeOrdHD
    ) where

import Data.Comp.Param.Multi.FreshM hiding (Name)
import Data.Comp.Param.Multi.Ordering
import Data.Comp.Derive.Utils
import Data.Maybe
import Data.List
import Language.Haskell.TH hiding (Cxt)
import Control.Monad (liftM)

compList :: [Ordering] -> Ordering
compList = fromMaybe EQ . find (/= EQ)

{-| Derive an instance of 'OrdHD' for a type constructor of any parametric
  kind taking at least three arguments. -}
makeOrdHD :: Name -> Q [Dec]
makeOrdHD fname = do
  TyConI (DataD _ name args constrs _) <- abstractNewtypeQ $ reify fname
  let args' = init args
  -- covariant argument
  let coArg :: Name = tyVarBndrName $ last args'
  -- contravariant argument
  let conArg :: Name = tyVarBndrName $ last $ init args'
  let argNames = map (VarT . tyVarBndrName) (init $ init args')
  let complType = foldl AppT (ConT name) argNames
  let classType = AppT (ConT ''OrdHD) complType
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  compareHDDecl <- funD 'compareHD (compareHDClauses conArg coArg constrs')
  let context = map (\arg -> ClassP ''Ord [arg]) argNames
  return [InstanceD context classType [compareHDDecl]]
      where compareHDClauses :: Name -> Name -> [(Name,[Type])] -> [ClauseQ]
            compareHDClauses _ _ [] = []
            compareHDClauses conArg coArg constrs = 
                let constrs' = constrs `zip` [1..]
                    constPairs = [(x,y)| x<-constrs', y <- constrs']
                in map (genClause conArg coArg) constPairs
            genClause conArg coArg ((c,n),(d,m))
                | n == m = genEqClause conArg coArg c
                | n < m = genLtClause c d
                | otherwise = genGtClause c d
            genEqClause :: Name -> Name -> (Name,[Type]) -> ClauseQ
            genEqClause conArg coArg (constr, args) = do 
              varXs <- newNames (length args) "x"
              varYs <- newNames (length args) "y"
              let patX = ConP constr $ map VarP varXs
              let patY = ConP constr $ map VarP varYs
              body <- eqDBody conArg coArg (zip3 varXs varYs args)
              return $ Clause [patX, patY] (NormalB body) []
            eqDBody :: Name -> Name -> [(Name, Name, Type)] -> ExpQ
            eqDBody conArg coArg x =
                [|liftM compList (sequence $(listE $ map (eqDB conArg coArg) x))|]
            eqDB :: Name -> Name -> (Name, Name, Type) -> ExpQ
            eqDB conArg coArg (x, y, tp)
                | not (containsType tp (VarT conArg)) &&
                  not (containsType tp (VarT coArg)) =
                    [| return $ compare $(varE x) $(varE y) |]
                | otherwise =
                    case tp of
                      AppT (VarT a) _ 
                          | a == coArg -> [| pcompare $(varE x) $(varE y) |]
                      AppT (AppT ArrowT (AppT (VarT a) _)) _
                          | a == conArg ->
                              [| withName (\v -> pcompare ($(varE x) $ nameCoerce v)
                                                          ($(varE y) $ nameCoerce v)) |]
                      SigT tp' _ ->
                          eqDB conArg coArg (x, y, tp')
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| compareHD $(varE x) $(varE y) |]
                          else
                              [| pcompare $(varE x) $(varE y) |]
            genLtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return LT |]) []
            genGtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return GT |]) []
