{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- |An instance of the first order logic type class Formulae which is
-- parameterized on the atomic predicate and atomic function types.
-- It is patterned after Logic-TPTP, but without the wrappers and
-- with some constructors like :~&: omitted.
module Logic.Instances.Parameterized
    ( Formula(..)
    , AtomicFormula(..)
    , Predicate
    , Proposition
    , Term(..)
    , V(..)
    ) where

import Data.Data (Data)
import Data.Monoid (Monoid(..))
import Data.String (IsString)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Class (FirstOrderLogic(..), Quant(..), PropositionalLogic(..), BinOp(..), InfixPred(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula p f
    = PredApp p [Term f]                      -- ^ Predicate application.  The terms are the free variables.
    | (:~:) (Formula p f)                     -- ^ Negation
    | BinOp (Formula p f) BinOp (Formula p f) -- ^ Binary connective application
    | InfixPred (Term f) InfixPred (Term f)   -- ^ Infix predicate application (equalities, inequalities)
    | Quant Quant [V] (Formula p f)           -- ^ Quantified formula
    -- A derived Eq instance is not going to tell us that a&b
    -- is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

type Predicate = Formula
type Proposition = Formula

-- | The range of a term is an element of a set.
data Term f
    = Var V                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [Term f]             -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Show,Read,Data,Typeable)
                
-- | Variable names
newtype V = V String
    deriving (Eq,Ord,Show,Data,Typeable,Read,Monoid,IsString)

-- |There is no atomic formula type in this data type, but we need one
-- to use as a parameter to the PropositionalLogic class.  The formulas
-- that are not generated from other formulas include those built using
-- the InfixPred and PredApp constructors, so we create a new type here
-- to represent the parameters to those two types.
data AtomicFormula term v p f
    = InfixPred' term InfixPred term
    | PredApp' p [term]
      deriving (Show, Eq)

instance (IsString f, Show p, Show f) => PropositionalLogic (Formula p f) (AtomicFormula (Term f) V p f) where
    x .<=>. y = BinOp  x (:<=>:) y
    x .=>.  y = BinOp  x (:=>:)  y
    x .|.   y = BinOp  x (:|:)   y
    x .&.   y = BinOp  x (:&:)   y
    (.~.) x   = (:~:) x
    atomic (InfixPred' t1 (:=:) t2) = t1 .=. t2
    atomic (InfixPred' t1 (:!=:) t2) = t1 .!=. t2
    atomic (PredApp' p ts) = pApp p ts
    foldF0 n b a formula =
        case formula of
          (:~:) x -> n x
          Quant _ _ _ -> error "foldF0: quantifiers should not be present"
          BinOp f1 op f2 -> b f1 op f2
          InfixPred t1 op t2 -> a (InfixPred' t1 op t2)
          PredApp p ts -> a (PredApp' p ts)

{-
foldFormula0 ::
                  (Formula p f -> r)
               -> (Formula p f -> BinOp -> Formula p f -> r)
               -> (Term f -> InfixPred -> Term f -> r)
               -> (p -> [Term f] -> r)
               -> Formula p f
               -> r
foldFormula0 kneg kbinop kinfix kpredapp f =
    case f of
      (:~:) x -> kneg x
      BinOp x y z -> kbinop x y z
      InfixPred x y z -> kinfix x y z
      PredApp x y -> kpredapp x y
      Quant _ _ _ -> error "foldFormula0: Quantifiers should not be present, use foldFormula"
-}

instance (PropositionalLogic (Formula p f) (AtomicFormula (Term f) V p f), Show p, Show f, IsString f) =>
         FirstOrderLogic (Formula p f) (AtomicFormula (Term f) V p f) (Term f) V p f where
    for_all vars x = Quant All vars x
    exists vars x = Quant Exists vars x
    foldF = foldFormula
    foldT = foldTerm
    pApp x args = PredApp x args
    var = Var
    fApp x args = FunApp x args
    toString (V s) = s
    x .=. y = InfixPred x (:=:) y
    x .!=. y = InfixPred x (:!=:) y

instance (IsString f, Show p, Show f) => Show (Formula p f) where
    show = showForm

foldFormula ::
                  (Formula p f -> r)
               -> (Quant -> [V] -> Formula p f -> r)
               -> (Formula p f -> BinOp -> Formula p f -> r)
               -> (Term f -> InfixPred -> Term f -> r)
               -> (p -> [Term f] -> r)
               -> Formula p f
               -> r
foldFormula kneg kquant kbinop kinfix kpredapp f =
    case f of
      (:~:) x -> kneg x
      Quant x y z -> kquant x y z
      BinOp x y z -> kbinop x y z
      InfixPred x y z -> kinfix x y z
      PredApp x y -> kpredapp x y
                      
foldTerm ::
               (V -> r)
            -> (f -> [Term f] -> r)
            -> Term f
            -> r
foldTerm kvar kfunapp t =
    case t of
      Var x -> kvar x
      FunApp x y -> kfunapp x y

-- |Versions of foldFormula and foldTerm to handle the wrapped types, which
-- were in TPTP but are not included in this system.
{-
foldF ::
           (Formula p f -> r) -- ^ Handle negation
         -> (Quant -> [V] -> Formula p f -> r) -- ^ Handle quantification
         -> (Formula p f -> BinOp -> Formula p f -> r) -- ^ Handle binary op
         -> (Term f -> InfixPred -> Term f -> r) -- ^ Handle equality/inequality
         -> (p -> [Term f] -> r) -- ^ Handle predicate symbol application
         -> (Formula p f -> r) -- ^ Handle formula
         
foldF kneg kquant kbinop kinfix kpredapp f = foldFormula kneg kquant kbinop kinfix kpredapp (unwrapF f)

-- | Eliminate terms
foldT ::
           (V -> r)             -- ^ Handle variable
         -> (f -> [Term f] -> r) -- ^ Handle function symbol application
         -> (Term f -> r)        -- ^ Handle term
foldT kvar kfunapp t = foldTerm kvar kfunapp (unwrapT t)

unwrapF = id
unwrapT = id
-}

instance Version (Term f)
instance Version V
instance Version (Formula p f)

$(deriveSerialize ''Term)
$(deriveSerialize ''V)
$(deriveSerialize ''Formula)

$(deriveNewData [''Term, ''V, ''Formula])
