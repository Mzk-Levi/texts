{-# LANGUAGE TemplateHaskell, TypeOperators, FlexibleInstances,
  FlexibleContexts, UndecidableInstances, GADTs, KindSignatures,
  OverlappingInstances, TypeSynonymInstances, EmptyDataDecls #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Examples.MultiParam.FOL
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- First-Order Logic a la Carte
--
-- This example illustrates how to implement First-Order Logic a la Carte
-- (Knowles, The Monad.Reader Issue 11, '08) using Generalised Parametric
-- Compositional Data Types.
--
-- Rather than using a fixed domain 'Term' for binders as Knowles, our encoding
-- uses a mutually recursive data structure for terms and formulae. This makes
-- terms modular too, and hence we only introduce variables when they are
-- actually needed in stage 5.
--
--------------------------------------------------------------------------------

module Examples.Multi.FOL where

import Data.Comp.Param.Multi hiding (Var)
import qualified Data.Comp.Param.Multi as MP
import Data.Comp.Param.Multi.Show ()
import Data.Comp.Param.Multi.Derive
import Data.Comp.Param.Multi.FreshM (Name, withName, evalFreshM)
import Data.List (intercalate)
import Data.Maybe
import Control.Monad.State
import Control.Monad.Reader

-- Phantom types indicating whether a (recursive) term is a formula or a term
data TFormula
data TTerm

-- Terms
data Const :: (* -> *) -> (* -> *) -> * -> * where
    Const :: String -> [e TTerm] -> Const a e TTerm
data Var :: (* -> *) -> (* -> *) -> * -> * where
    Var :: String -> Var a e TTerm

-- Formulae
data TT :: (* -> *) -> (* -> *) -> * -> * where
    TT :: TT a e TFormula
data FF :: (* -> *) -> (* -> *) -> * -> * where
    FF :: FF a e TFormula
data Atom :: (* -> *) -> (* -> *) -> * -> * where
    Atom :: String -> [e TTerm] -> Atom a e TFormula
data NAtom :: (* -> *) -> (* -> *) -> * -> * where
    NAtom :: String -> [e TTerm] -> NAtom a e TFormula
data Not :: (* -> *) -> (* -> *) -> * -> * where
    Not :: e TFormula -> Not a e TFormula
data Or :: (* -> *) -> (* -> *) -> * -> * where
    Or :: e TFormula -> e TFormula -> Or a e TFormula
data And :: (* -> *) -> (* -> *) -> * -> * where
    And :: e TFormula -> e TFormula -> And a e TFormula
data Impl :: (* -> *) -> (* -> *) -> * -> * where
    Impl :: e TFormula -> e TFormula -> Impl a e TFormula
data Exists :: (* -> *) -> (* -> *) -> * -> * where
    Exists :: (a TTerm -> e TFormula) -> Exists a e TFormula
data Forall :: (* -> *) -> (* -> *) -> * -> * where
    Forall :: (a TTerm -> e TFormula) -> Forall a e TFormula

$(derive [makeHDifunctor, smartConstructors]
         [''Const, ''Var, ''TT, ''FF, ''Atom, ''NAtom,
          ''Not, ''Or, ''And, ''Impl, ''Exists, ''Forall])

--------------------------------------------------------------------------------
-- (Custom) pretty printing of terms and formulae
--------------------------------------------------------------------------------

instance ShowHD Const where
  showHD (Const f t) = do ts <- mapM unK t
                          return $ f ++ "(" ++ intercalate ", " ts ++ ")"

instance ShowHD Var where
  showHD (Var x) = return x

instance ShowHD TT where
  showHD TT = return "true"

instance ShowHD FF where
  showHD FF = return "false"

instance ShowHD Atom where
  showHD (Atom p t) = do ts <- mapM unK t
                         return $ p ++ "(" ++ intercalate ", " ts ++ ")"

instance ShowHD NAtom where
  showHD (NAtom p t) = do ts <- mapM unK t
                          return $ "not " ++ p ++ "(" ++ intercalate ", " ts ++ ")"

instance ShowHD Not where
  showHD (Not (K f)) = liftM (\x -> "not (" ++ x ++ ")") f

instance ShowHD Or where
  showHD (Or (K f1) (K f2)) =
      liftM2 (\x y -> "(" ++ x ++ ") or (" ++ y ++ ")") f1 f2

instance ShowHD And where
  showHD (And (K f1) (K f2)) =
      liftM2 (\x y -> "(" ++ x ++ ") and (" ++ y ++ ")") f1 f2

instance ShowHD Impl where
  showHD (Impl (K f1) (K f2)) =
      liftM2 (\x y -> "(" ++ x ++ ") -> (" ++ y ++ ")") f1 f2

instance ShowHD Exists where
  showHD (Exists f) =
      withName (\x -> do b <- unK (f x)
                         return $ "exists " ++ show x ++ ". " ++ b)

instance ShowHD Forall where
  showHD (Forall f) =
      withName (\x -> do b <- unK (f x)
                         return $ "forall " ++ show x ++ ". " ++ b)

--------------------------------------------------------------------------------
-- Stage 0
--------------------------------------------------------------------------------

type Input = Const :+:
             TT :+: FF :+: Atom :+: Not :+: Or :+: And :+: Impl :+:
             Exists :+: Forall

foodFact :: Term Input TFormula
foodFact = Term $
  iExists (\p -> iAtom "Person" [p] `iAnd`
                 iForall (\f -> iAtom "Food" [f] `iImpl`
                                iAtom "Eats" [p,f])) `iImpl`
  iNot (iExists $ \f -> iAtom "Food" [f] `iAnd`
                        iNot (iExists $ \p -> iAtom "Person" [p] `iAnd`
                                              iAtom "Eats" [p,f]))

--------------------------------------------------------------------------------
-- Stage 1: Eliminate Implications
--------------------------------------------------------------------------------

type Stage1 = Const :+:
              TT :+: FF :+: Atom :+: Not :+: Or :+: And :+: Exists :+: Forall

class HDifunctor f => ElimImp f where
  elimImpHom :: Hom f Stage1

$(derive [liftSum] [''ElimImp])

elimImp :: Term Input :-> Term Stage1
elimImp (Term t) = Term (appHom elimImpHom t)

instance (HDifunctor f, f :<: Stage1) => ElimImp f where
  elimImpHom = simpCxt . inj

instance ElimImp Impl where
  elimImpHom (Impl f1 f2) = iNot (Hole f1) `iOr` (Hole f2)

foodFact1 :: Term Stage1 TFormula
foodFact1 = elimImp foodFact

--------------------------------------------------------------------------------
-- Stage 2: Move Negation Inwards
--------------------------------------------------------------------------------

type Stage2 = Const :+:
              TT :+: FF :+: Atom :+: NAtom :+: Or :+: And :+: Exists :+: Forall

class HDifunctor f => Dualize f where
  dualizeHom :: f a (Cxt h Stage2 a b) :-> Cxt h Stage2 a b

$(derive [liftSum] [''Dualize])

dualize :: Trm Stage2 a :-> Trm Stage2 a
dualize = appHom (dualizeHom . hfmap Hole)

instance Dualize Const where
  dualizeHom (Const f t) = iConst f t

instance Dualize TT where
  dualizeHom TT = iFF

instance Dualize FF where
  dualizeHom FF = iTT

instance Dualize Atom where
  dualizeHom (Atom p t) = iNAtom p t

instance Dualize NAtom where
  dualizeHom (NAtom p t) = iAtom p t

instance Dualize Or where
  dualizeHom (Or f1 f2) = f1 `iAnd` f2

instance Dualize And where
  dualizeHom (And f1 f2) = f1 `iOr` f2

instance Dualize Exists where
  dualizeHom (Exists f) = inject $ Forall f

instance Dualize Forall where
  dualizeHom (Forall f) = inject $ Exists f

class PushNot f where
  pushNotAlg :: Alg f (Trm Stage2 a)

$(derive [liftSum] [''PushNot])

pushNotInwards :: Term Stage1 :-> Term Stage2
pushNotInwards t = Term (cata pushNotAlg t)

instance (HDifunctor f, f :<: Stage2) => PushNot f where
  pushNotAlg = inject . hdimap MP.Var id -- default

instance PushNot Not where
  pushNotAlg (Not f) = dualize f

foodFact2 :: Term Stage2 TFormula
foodFact2 = pushNotInwards foodFact1

--------------------------------------------------------------------------------
-- Stage 4: Skolemization
--------------------------------------------------------------------------------

type Stage4 = Const :+:
              TT :+: FF :+: Atom :+: NAtom :+: Or :+: And :+: Forall

type Unique = Int
data UniqueSupply = UniqueSupply Unique UniqueSupply UniqueSupply

initialUniqueSupply :: UniqueSupply
initialUniqueSupply = genSupply 1
    where genSupply n = UniqueSupply n (genSupply (2 * n))
                                       (genSupply (2 * n + 1))

splitUniqueSupply :: UniqueSupply -> (UniqueSupply, UniqueSupply)
splitUniqueSupply (UniqueSupply	_ l r) = (l,r)

getUnique :: UniqueSupply -> (Unique, UniqueSupply)
getUnique (UniqueSupply n l _) = (n,l)

type Supply = State UniqueSupply
type S a = ReaderT [Trm Stage4 a TTerm] Supply

evalS :: S a b -> [Trm Stage4 a TTerm] -> UniqueSupply -> b
evalS m env = evalState (runReaderT m env)

fresh :: S a Int
fresh = do supply <- get
           let (uniq,rest) = getUnique supply
           put rest
           return uniq

freshes :: S a UniqueSupply
freshes = do supply <- get
             let (l,r) = splitUniqueSupply supply
             put r
             return l

class Skolem f where
  skolemAlg :: AlgM' (S a) f (Trm Stage4 a)

$(derive [liftSum] [''Skolem])

skolemize :: Term Stage2 :-> Term Stage4
skolemize f = Term (evalState (runReaderT (cataM' skolemAlg f) [])
                              initialUniqueSupply)

instance Skolem Const where
  skolemAlg (Const f t) = liftM (iConst f) $ mapM getCompose t

instance Skolem TT where
  skolemAlg TT = return iTT

instance Skolem FF where
  skolemAlg FF = return iFF

instance Skolem Atom where
  skolemAlg (Atom p t) = liftM (iAtom p) $ mapM getCompose t

instance Skolem NAtom where
  skolemAlg (NAtom p t) = liftM (iNAtom p) $ mapM getCompose t

instance Skolem Or where
  skolemAlg (Or (Compose f1) (Compose f2)) = liftM2 iOr f1 f2

instance Skolem And where
  skolemAlg (And (Compose f1) (Compose f2)) = liftM2 iAnd f1 f2

instance Skolem Forall where
  skolemAlg (Forall f) = do
    supply <- freshes
    xs <- ask
    return $ iForall $ \x -> evalS (getCompose $ f x) (x : xs) supply

instance Skolem Exists where
  skolemAlg (Exists f) = do
    uniq <- fresh
    xs <- ask
    getCompose $ f (iConst ("Skol" ++ show uniq) xs)

foodFact4 :: Term Stage4 TFormula
foodFact4 = skolemize foodFact2

--------------------------------------------------------------------------------
-- Stage 5: Prenex Normal Form
--------------------------------------------------------------------------------

type Stage5 = Const :+: Var :+:
              TT :+: FF :+: Atom :+: NAtom :+: Or :+: And

class Prenex f where
  prenexAlg :: AlgM' (S a) f (Trm Stage5 a)

$(derive [liftSum] [''Prenex])

prenex :: Term Stage4 :-> Term Stage5
prenex f = Term (evalState (runReaderT (cataM' prenexAlg f) [])
                           initialUniqueSupply)

instance Prenex Const where
  prenexAlg (Const f t) = liftM (iConst f) $ mapM getCompose t

instance Prenex TT where
  prenexAlg TT = return iTT

instance Prenex FF where
  prenexAlg FF = return iFF

instance Prenex Atom where
  prenexAlg (Atom p t) = liftM (iAtom p) $ mapM getCompose t

instance Prenex NAtom where
  prenexAlg (NAtom p t) = liftM (iNAtom p) $ mapM getCompose t

instance Prenex Or where
  prenexAlg (Or (Compose f1) (Compose f2)) = liftM2 iOr f1 f2

instance Prenex And where
  prenexAlg (And (Compose f1) (Compose f2)) = liftM2 iAnd f1 f2

instance Prenex Forall where
  prenexAlg (Forall f) = do uniq <- fresh
                            getCompose $ f (iVar ('x' : show uniq))

foodFact5 :: Term Stage5 TFormula
foodFact5 = prenex foodFact4

--------------------------------------------------------------------------------
-- Stage 6: Conjunctive Normal Form
--------------------------------------------------------------------------------

type Literal a     = Trm (Const :+: Var :+: Atom :+: NAtom) a
newtype Clause a i = Clause {unClause :: [Literal a i]} -- implicit disjunction
newtype CNF a i    = CNF {unCNF :: [Clause a i]}        -- implicit conjunction

instance (HDifunctor f, ShowHD f) => Show (Trm f Name i) where
  show = evalFreshM . showHD . toCxt

instance Show (Clause Name i) where
  show c = intercalate " or " $ map show $ unClause c

instance Show (CNF Name i) where
  show c = intercalate "\n" $ map show $ unCNF c

class ToCNF f where
  cnfAlg :: f (CNF a) (CNF a) i -> [Clause a i]

$(derive [liftSum] [''ToCNF])

cnf :: Term Stage5 :-> CNF a
cnf = cata (CNF . cnfAlg)

instance ToCNF Const where
  cnfAlg (Const f t) =
      [Clause [iConst f (map (head . unClause . head . unCNF) t)]]

instance ToCNF Var where
  cnfAlg (Var x) = [Clause [iVar x]]

instance ToCNF TT where
  cnfAlg TT = []

instance ToCNF FF where
  cnfAlg FF = [Clause []]

instance ToCNF Atom where
  cnfAlg (Atom p t) =
      [Clause [iAtom p (map (head . unClause . head . unCNF) t)]]

instance ToCNF NAtom where
  cnfAlg (NAtom p t) =
      [Clause [iNAtom p (map (head . unClause . head . unCNF) t)]]

instance ToCNF And where
  cnfAlg (And f1 f2) = unCNF f1 ++ unCNF f2

instance ToCNF Or where
  cnfAlg (Or f1 f2) =
      [Clause (x ++ y) | Clause x <- unCNF f1, Clause y <- unCNF f2]

foodFact6 :: CNF a TFormula
foodFact6 = cnf foodFact5

--------------------------------------------------------------------------------
-- Stage 7: Implicative Normal Form
--------------------------------------------------------------------------------

type T              = Const :+: Var :+: Atom :+: NAtom
newtype IClause a i = IClause ([Trm T a i], -- implicit conjunction
                               [Trm T a i]) -- implicit disjunction
newtype INF a i     = INF [IClause a i]     -- implicit conjunction

instance Show (IClause Name i) where
  show (IClause (cs,ds)) = let cs' = intercalate " and " $ map show cs
                               ds' = intercalate " or " $ map show ds
                           in "(" ++ cs' ++ ") -> (" ++ ds' ++ ")"

instance Show (INF Name i) where
  show (INF fs) = intercalate "\n" $ map show fs

inf :: CNF a TFormula -> INF a TFormula
inf (CNF f) = INF $ map (toImpl . unClause) f
    where toImpl :: [Literal a TFormula] -> IClause a TFormula
          toImpl disj = IClause ([iAtom p t | NAtom p t <- mapMaybe proj1 disj],
                                 [inject t | t <- mapMaybe proj2 disj])
          proj1 :: NatM Maybe (Trm T a) (NAtom a (Trm T a))
          proj1 = project
          proj2 :: NatM Maybe (Trm T a) (Atom a (Trm T a))
          proj2 = project

foodFact7 :: INF a TFormula
foodFact7 = inf foodFact6
