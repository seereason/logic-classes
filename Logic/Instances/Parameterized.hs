{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- |An instance of the first order logic type class Formulae which is
-- parameterized on the atomic predicate and atomic function types.
-- It is patterned after Logic-TPTP, but without the wrappers and
-- with some constructors like :~&: omitted.
module Logic.Instances.Parameterized
    ( Formula(..)
    , Predicate
    , Proposition
    , Term(..)
    ) where

import Data.Data (Data)
import Data.String (IsString(..))
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.FirstOrder (FirstOrderLogic(..), Quant(..), InfixPred(..), Boolean(..), Skolem(..))
import Logic.Logic (Logic(..), BinOp(..))
import Logic.Propositional (PropositionalLogic(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = PredApp p [Term v f]                        -- ^ Predicate application.  The terms are the free variables.
    | (:~:) (Formula v p f)                       -- ^ Negation
    | BinOp (Formula v p f) BinOp (Formula v p f) -- ^ Binary connective application
    | InfixPred (Term v f) InfixPred (Term v f)   -- ^ Infix predicate application (equalities, inequalities)
    | Quant Quant [v] (Formula v p f)             -- ^ Quantified formula
    -- A derived Eq instance is not going to tell us that a&b
    -- is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

type Predicate = Formula
type Proposition = Formula

-- | The range of a term is an element of a set.
data Term v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [Term v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Logic (Formula v p f) where
    x .<=>. y = BinOp  x (:<=>:) y
    x .=>.  y = BinOp  x (:=>:)  y
    x .|.   y = BinOp  x (:|:)   y
    x .&.   y = BinOp  x (:&:)   y
    (.~.) x   = (:~:) x

instance (Logic (Formula v p f), Ord v, IsString v, Eq p, Boolean p, Eq f, Skolem f, Show p, Show f) =>
         PropositionalLogic (Formula v p f) (Formula v p f) where
    atomic (InfixPred t1 (:=:) t2) = t1 .=. t2
    atomic (InfixPred t1 (:!=:) t2) = t1 .!=. t2
    atomic (PredApp p ts) = pApp p ts
    atomic _ = error "atomic method of PropositionalLogic for Parameterized: invalid argument"
    foldF0 n b a formula =
        case formula of
          (:~:) x -> n x
          Quant _ _ _ -> error "foldF0: quantifiers should not be present"
          BinOp f1 op f2 -> b f1 op f2
          InfixPred t1 op t2 -> a (InfixPred t1 op t2)
          PredApp p ts -> a (PredApp p ts)

instance (PropositionalLogic (Formula v p f) (Formula v p f), Ord v, IsString v, Eq p, Boolean p, Eq f, Skolem f, Show p, Show f) =>
          FirstOrderLogic (Formula v p f) (Term v f) v p f where
    for_all vars x = Quant All vars x
    exists vars x = Quant Exists vars x
    foldF = foldFormula
    foldT = foldTerm
    pApp x args = PredApp x args
    var = Var
    fApp x args = FunApp x args
    x .=. y = InfixPred x (:=:) y
    x .!=. y = InfixPred x (:!=:) y

foldFormula ::
                  (Formula v p f -> r)
               -> (Quant -> [v] -> Formula v p f -> r)
               -> (Formula v p f -> BinOp -> Formula v p f -> r)
               -> (Term v f -> InfixPred -> Term v f -> r)
               -> (p -> [Term v f] -> r)
               -> Formula v p f
               -> r
foldFormula kneg kquant kbinop kinfix kpredapp f =
    case f of
      (:~:) x -> kneg x
      Quant x y z -> kquant x y z
      BinOp x y z -> kbinop x y z
      InfixPred x y z -> kinfix x y z
      PredApp x y -> kpredapp x y
                      
foldTerm ::
               (v -> r)
            -> (f -> [Term v f] -> r)
            -> Term v f
            -> r
foldTerm kvar kfunapp t =
    case t of
      Var x -> kvar x
      FunApp x y -> kfunapp x y

instance Version (Term v f)
instance Version (Formula v p f)

$(deriveSerialize ''Term)
$(deriveSerialize ''Formula)

$(deriveNewData [''Term, ''Formula])
