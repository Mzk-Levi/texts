{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.SmartAConstructors
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors with annotations for difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.SmartAConstructors 
    (
     smartAConstructors
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Param.Ops
import Data.Comp.Param.Term
import Data.Comp.Param.Difunctor

import Control.Monad

{-| Derive smart constructors with annotations for a difunctor. The smart
 constructors are similar to the ordinary constructors, but a
 'injectA . dimap Var id' is automatically inserted. -}
smartAConstructors :: Name -> Q [Dec]
smartAConstructors fname = do
    TyConI (DataD _cxt _tname _targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM genSmartConstr cons
        where genSmartConstr (name, args) = do
                let bname = nameBase name
                genSmartConstr' (mkName $ "iA" ++ bname) name args
              genSmartConstr' sname name args = do
                varNs <- newNames args "x"
                varPr <- newName "_p"
                let pats = map varP (varPr : varNs)
                    vars = map varE varNs
                    val = appE [|injectA $(varE varPr)|] $
                          appE [|inj . dimap Var id|] $ foldl appE (conE name) vars
                    function = [funD sname [clause pats (normalB [|In $val|]) []]]
                sequence function
