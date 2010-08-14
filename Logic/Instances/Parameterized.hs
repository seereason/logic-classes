{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- |An instance of the first order logic type class Formulae which is
-- parameterized on the atomic predicate and atomic function types.
-- It is patterned after Logic-TPTP, but without the wrappers and
-- with some constructors like :~&: omitted.
module Logic.Instances.Parameterized
    ( Formula(..)
    , PTerm(..)
    ) where

import Data.Data (Data)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.FirstOrder (Term(..), FirstOrderLogic(..), Quant(..), InfixPred(..), Skolem(..))
import Logic.Logic (Logic(..), BinOp(..), Boolean(..))
import Logic.Propositional (PropositionalLogic(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = PredApp p [PTerm v f]                        -- ^ Predicate application.  The terms are the free variables.
    | (:~:) (Formula v p f)                       -- ^ Negation
    | BinOp (Formula v p f) BinOp (Formula v p f) -- ^ Binary connective application
    | InfixPred (PTerm v f) InfixPred (PTerm v f)   -- ^ Infix predicate application (equalities, inequalities)
    | Quant Quant [v] (Formula v p f)             -- ^ Quantified formula
    -- A derived Eq instance is not going to tell us that a&b
    -- is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

-- | The range of a term is an element of a set.
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
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

instance (Logic (Formula v p f), Ord v, Enum v, Data v, Eq p, Boolean p, Data p, Eq f, Skolem f, Data f) =>
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

instance (Ord v, Enum v, Data v, Eq f, Skolem f, Data f) => Term (PTerm v f) v f where
    foldT = foldTerm
    zipT v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FunApp f1 ts1, FunApp f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Var
    fApp x args = FunApp x args

instance (PropositionalLogic (Formula v p f) (Formula v p f), Term (PTerm v f) v f, Ord v, Enum v, Data v, Eq p, Boolean p, Data p, Eq f, Skolem f, Data f) =>
          FirstOrderLogic (Formula v p f) (PTerm v f) v p f where
    for_all vars x = Quant All vars x
    exists vars x = Quant Exists vars x
    foldF = foldFormula
    zipF n q b i p f1 f2 =
        case (f1, f2) of
          ((:~:) f1', (:~:) f2') -> n f1' f2' 
          (Quant q1 vs1 f1', Quant q2 vs2 f2') -> q q1 vs1 f1' q2 vs2 f2'
          (BinOp l1 op1 r1, BinOp l2 op2 r2) -> b l1 op1 r1 l2 op2 r2
          (InfixPred l1 op1 r1, InfixPred l2 op2 r2) -> i l1 op1 r1 l2 op2 r2
          (PredApp p1 ts1, PredApp p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp x args = PredApp x args
    x .=. y = InfixPred x (:=:) y
    x .!=. y = InfixPred x (:!=:) y

foldFormula ::
                  (Formula v p f -> r)
               -> (Quant -> [v] -> Formula v p f -> r)
               -> (Formula v p f -> BinOp -> Formula v p f -> r)
               -> (PTerm v f -> InfixPred -> PTerm v f -> r)
               -> (p -> [PTerm v f] -> r)
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
            -> (f -> [PTerm v f] -> r)
            -> PTerm v f
            -> r
foldTerm kvar kfunapp t =
    case t of
      Var x -> kvar x
      FunApp x y -> kfunapp x y

instance Version (PTerm v f)
instance Version (Formula v p f)

$(deriveSerialize ''PTerm)
$(deriveSerialize ''Formula)

$(deriveNewData [''PTerm, ''Formula])
