{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Param.Derive.SmartConstructors
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors for difunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Param.Derive.SmartConstructors 
    (
     smartConstructors
    ) where

import Language.Haskell.TH hiding (Cxt)
import Data.Comp.Derive.Utils
import Data.Comp.Param.Sum
import Data.Comp.Param.Term
import Data.Comp.Param.Difunctor
import Control.Monad

{-| Derive smart constructors for a difunctor. The smart constructors are
 similar to the ordinary constructors, but a 'inject . dimap Var id' is
 automatically inserted. -}
smartConstructors :: Name -> Q [Dec]
smartConstructors fname = do
    TyConI (DataD _cxt tname targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    liftM concat $ mapM (genSmartConstr (map tyVarBndrName targs) tname) cons
        where genSmartConstr targs tname (name, args) = do
                let bname = nameBase name
                genSmartConstr' targs tname (mkName $ 'i' : bname) name args
              genSmartConstr' targs tname sname name args = do
                varNs <- newNames args "x"
                let pats = map varP varNs
                    vars = map varE varNs
                    val = foldl appE (conE name) vars
                    sig = genSig targs tname sname args
                    function = [funD sname [clause pats (normalB [|inject (dimap Var id $val)|]) []]]
                sequence $ sig ++ function
              genSig targs tname sname 0 = (:[]) $ do
                hvar <- newName "h"
                fvar <- newName "f"
                avar <- newName "a"
                bvar <- newName "b"
                let targs' = init $ init targs
                    vars = hvar:fvar:avar:bvar:targs'
                    h = varT hvar
                    f = varT fvar
                    a = varT avar
                    b = varT bvar
                    ftype = foldl appT (conT tname) (map varT targs')
                    constr = classP ''(:<:) [ftype, f]
                    typ = foldl appT (conT ''Cxt) [h, f, a, b]
                    typeSig = forallT (map PlainTV vars) (sequence [constr]) typ
                sigD sname typeSig
              genSig _ _ _ _ = []