{-# LANGUAGE TemplateHaskell, FlexibleInstances, IncoherentInstances,
  ScopedTypeVariables #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.Ordering
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @OrdD@.
--
--------------------------------------------------------------------------------
module Data.Comp.Param.Derive.Ordering
    (
     OrdD(..),
     makeOrdD
    ) where

import Data.Comp.Param.FreshM hiding (Name)
import Data.Comp.Param.Ordering
import Data.Comp.Derive.Utils
import Language.Haskell.TH hiding (Cxt)
import Control.Monad (liftM)

{-| Derive an instance of 'OrdD' for a type constructor of any parametric
  kind taking at least two arguments. -}
makeOrdD :: Name -> Q [Dec]
makeOrdD fname = do
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
  let classType = AppT (ConT ''OrdD) complType
  -- constrs' = [(X,[c]), (Y,[a,c]), (Z,[b -> c])]
  constrs' :: [(Name,[Type])] <- mapM normalConExp constrs
  compareDDecl <- funD 'compareD (compareDClauses conArg coArg constrs')
  let context = map (\arg -> ClassP ''Ord [arg]) argNames
  return [InstanceD context classType [compareDDecl]]
      where compareDClauses :: Name -> Name -> [(Name,[Type])] -> [ClauseQ]
            compareDClauses _ _ [] = []
            compareDClauses conArg coArg constrs = 
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
                      VarT a
                          | a == coArg -> [| pcompare $(varE x) $(varE y) |]
                      AppT (AppT ArrowT (VarT a)) _
                          | a == conArg ->
                              [| withName (\v -> pcompare ($(varE x) v) ($(varE y) v)) |]
                      SigT tp' _ ->
                          eqDB conArg coArg (x, y, tp')
                      _ ->
                          if containsType tp (VarT conArg) then
                              [| compareD $(varE x) $(varE y) |]
                          else
                              [| pcompare $(varE x) $(varE y) |]
            genLtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return LT |]) []
            genGtClause (c, _) (d, _) =
                clause [recP c [], recP d []] (normalB [| return GT |]) []