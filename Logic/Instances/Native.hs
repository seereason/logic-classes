{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
-- |Data types which are instances of the Logic type class for use
-- when you just want to use the classes and you don't have a
-- particular representation you need to use.
module Logic.Instances.Native
    ( Formula(..)
    , PTerm(..)
    , ImplicativeNormalForm(..)
    ) where

import Data.Data (Data)
import qualified Data.Set as S
import Data.String (IsString)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.FirstOrder (Term(..), FirstOrderLogic(..), Quant(..), InfixPred(..), Skolem(..), Pretty, quant', showForm, showTerm)
import Logic.Implicative (Implicative(..))
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
    deriving (Eq,Ord,Read,Data,Typeable)

instance (FirstOrderLogic (Formula v p f) (PTerm v f) v p f, Show v, Show p, Show f) => Show (Formula v p f) where
    show = showForm

instance (FirstOrderLogic (Formula v p f) (PTerm v f) v p f, Show v, Show p, Show f) => Show (PTerm v f) where
    show = showTerm

data ImplicativeNormalForm v p f =
    INF (S.Set (Formula v p f)) (S.Set (Formula v p f))
    deriving (Eq, Data, Typeable)

instance (Ord v, IsString v, Enum v, Data v, Pretty v, Show v,
          Ord p, IsString p, Boolean p, Data p, Pretty p, Show p,
          Ord f, IsString f, Skolem f, Data f, Pretty f, Show f,
          Show (Formula v p f)) => Implicative (ImplicativeNormalForm v p f) (Formula v p f) where
    neg (INF lhs _) = lhs
    pos (INF _ rhs) = rhs
    makeINF = INF

instance (FirstOrderLogic (Formula v p f) (PTerm v f) v p f, Show (Formula v p f)) => Show (ImplicativeNormalForm v p f) where
    show x = "makeINF (" ++ show (neg x) ++ ") (" ++ show (pos x) ++ ")"
    
instance Logic (Formula v p f) where
    x .<=>. y = BinOp  x (:<=>:) y
    x .=>.  y = BinOp  x (:=>:)  y
    x .|.   y = BinOp  x (:|:)   y
    x .&.   y = BinOp  x (:&:)   y
    (.~.) x   = (:~:) x

instance (Ord v, IsString v, Enum v, Data v, Pretty v, Show v,
          Ord p, IsString p, Boolean p, Data p, Pretty p, Show p,
          Ord f, IsString f, Skolem f, Data f, Pretty f, Show f,
          Logic (Formula v p f), Show (Formula v p f)) =>
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
    foldT vf fn t =
        case t of
          Var v -> vf v
          FunApp f ts -> fn f ts
    zipT v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FunApp f1 ts1, FunApp f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Var
    fApp x args = FunApp x args

instance (Ord v, IsString v, Enum v, Data v, Pretty v, Show v,
          Ord p, IsString p, Boolean p, Data p, Pretty p,  Show p,
          Ord f, IsString f, Skolem f, Data f, Pretty f, Show f,
          Show (Formula v p f),
          PropositionalLogic (Formula v p f) (Formula v p f), Term (PTerm v f) v f) =>
          FirstOrderLogic (Formula v p f) (PTerm v f) v p f where
    for_all v x = Quant All [v] x
    exists v x = Quant Exists [v] x
    foldF n q b i p f =
        case f of
          (:~:) f' -> n f'
          -- Be careful not to create quants with empty variable lists
          Quant op (v:vs) f' -> q op v (quant' op vs f')
          Quant _ [] f' -> foldF n q b i p f'
          BinOp l op r -> b l op r
          InfixPred l op r -> i l op r
          PredApp pr ts -> p pr ts
    zipF n q b i p f1 f2 =
        case (f1, f2) of
          ((:~:) f1', (:~:) f2') -> n f1' f2' 
          (Quant q1 (v1:vs1) f1', Quant q2 (v2:vs2) f2') -> q q1 v1 (Quant q1 vs1 f1') q2 v2 (Quant q2 vs2 f2')
          (Quant _ [] f1', Quant _ [] f2') -> zipF n q b i p f1' f2'
          (BinOp l1 op1 r1, BinOp l2 op2 r2) -> b l1 op1 r1 l2 op2 r2
          (InfixPred l1 op1 r1, InfixPred l2 op2 r2) -> i l1 op1 r1 l2 op2 r2
          (PredApp p1 ts1, PredApp p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp x args = PredApp x args
    x .=. y = InfixPred x (:=:) y
    x .!=. y = InfixPred x (:!=:) y

instance Version (PTerm v f)
instance Version (Formula v p f)

$(deriveSerialize ''PTerm)
$(deriveSerialize ''Formula)

$(deriveNewData [''PTerm, ''Formula])
