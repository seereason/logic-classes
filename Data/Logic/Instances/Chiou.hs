{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-orphans -fno-warn-missing-signatures #-}
module Data.Logic.Instances.Chiou
    ( Sentence(..)
    , CTerm(..)
    , Connective(..)
    , Quantifier(..)
    , ConjunctiveNormalForm(..)
    , NormalSentence(..)
    , NormalTerm(..)
    , toSentence
    , fromSentence
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Arity (Arity)
import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combinable(..), BinOp(..), Combination(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Equals (AtomEq(..), (.=.), PredicateEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..), quant', pApp)
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Term (Term(..), Function)
import qualified Data.Logic.Classes.FirstOrder as L
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Variable (Variable(prefix, prettyVariable))
import Data.String (IsString(..))

data Sentence v p f
    = Connective (Sentence v p f) Connective (Sentence v p f)
    | Quantifier Quantifier [v] (Sentence v p f)
    | Not (Sentence v p f)
    | Predicate p [CTerm v f]
    | Equal (CTerm v f) (CTerm v f)
    deriving (Eq, Ord, Data, Typeable)

data CTerm v f
    = Function f [CTerm v f]
    | Variable v
    deriving (Eq, Ord, Data, Typeable)

data Connective
    = Imply
    | Equiv
    | And
    | Or
    deriving (Eq, Ord, Show, Data, Typeable)

data Quantifier
    = ForAll
    | ExistsCh
    deriving (Eq, Ord, Show, Data, Typeable)

instance Negatable (Sentence v p f) where
    (.~.) (Not (Not x)) = (.~.) x
    (.~.) (Not x) = x
    (.~.) x   = Not x
    negated (Not x) = not (negated x)
    negated _ = False

instance (Constants (Sentence v p f), Ord v, Ord p, Ord f) => Combinable (Sentence v p f) where
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y

instance (Ord v, IsString v, Data v, Variable v, 
          Ord p, IsString p, Data p, Constants p, Arity p,
          Ord f, IsString f, Data f, Skolem f, 
          Constants (Sentence v p f), Combinable (Sentence v p f)) =>
         PropositionalFormula (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic x@(Predicate _ _) = x
    atomic x@(Equal _ _) = x
    foldPropositional c a formula =
        case formula of
          Not x -> c ((:~:) x)
          Quantifier _ _ _ -> error "Logic.Instance.Chiou.foldF0: unexpected"
          Connective f1 Imply f2 -> c (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> c (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> c (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> c (BinOp f1 (:|:) f2)
          Predicate p ts -> a (Predicate p ts)
          Equal t1 t2 -> a (Equal t1 t2)

data AtomicFunction
    = AtomicFunction String
    -- This is redundant with the SkolemFunction and SkolemConstant
    -- constructors in the Chiou Term type.
    | AtomicSkolemFunction Int
    deriving (Eq, Show)

instance IsString AtomicFunction where
    fromString = AtomicFunction

instance Skolem AtomicFunction where
    toSkolem = AtomicSkolemFunction 
    fromSkolem (AtomicSkolemFunction n) = Just n
    fromSkolem _ = Nothing

-- The Atom type is not cleanly distinguished from the Sentence type, so we need an Atom instance for Sentence.
instance (Constants (Sentence v p f), Ord v, Ord p, Arity p, Constants p, Ord f) => Atom (Sentence v p f) p (CTerm v f) where
    foldAtom ap (Predicate p ts) = ap p ts
    foldAtom _ _ = error "Data.Logic.Instances.Chiou: Invalid atom"
    zipAtoms ap (Predicate p1 ts1) (Predicate p2 ts2) = ap p1 ts1 p2 ts2
    zipAtoms _ _ _ = Nothing
    apply' = Predicate

instance (Arity p, PredicateEq p, Show p) => AtomEq (Sentence v p f) p (CTerm v f) where
    foldAtomEq ap _ (Predicate p ts) = ap p ts
    foldAtomEq _ eq (Equal t1 t2) = eq t1 t2
    foldAtomEq _ _ _ = error "Data.Logic.Instances.Chiou: Invalid atom"
    zipAtomsEq ap _ (Predicate p1 ts1) (Predicate p2 ts2) = ap p1 ts1 p2 ts2
    zipAtomsEq _ eq (Equal t1 t2) (Equal t3 t4) = eq t1 t2 t3 t4
    zipAtomsEq _ _ _ _ = Nothing
    equals = Equal
    applyEq' = Predicate

instance (Ord v, IsString v, Variable v, Data v, Show v,
          Ord p, IsString p, Constants p, Arity p, Data p, Show p,
          Ord f, IsString f, Skolem f, Data f, Show f,
          PropositionalFormula (Sentence v p f) (Sentence v p f)) =>
          FirstOrderFormula (Sentence v p f) (Sentence v p f) v where
    for_all v x = Quantifier ForAll [v] x
    exists v x = Quantifier ExistsCh [v] x
    foldFirstOrder q c p f =
        case f of
          Not x -> c ((:~:) x)
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> Forall
                          ExistsCh -> Exists in
              -- Use Logic.quant' here instead of the constructor
              -- Quantifier so as not to create quantifications with
              -- empty variable lists.
              q op' v (quant' op' vs f')
          Quantifier _ [] f' -> foldFirstOrder q c p f'
          Connective f1 Imply f2 -> c (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> c (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> c (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> c (BinOp f1 (:|:) f2)
          Predicate _ _ -> p f
          Equal _ _ -> p f
    zipFirstOrder q c p f1 f2 =
        case (f1, f2) of
          (Not f1', Not f2') -> c ((:~:) f1') ((:~:) f2')
          (Quantifier op1 (v1:vs1) f1', Quantifier op2 (v2:vs2) f2') ->
              if op1 == op2
              then let op' = case op1 of
                               ForAll -> Forall
                               ExistsCh -> Exists in
                   q op' v1 (Quantifier op1 vs1 f1') Forall v2 (Quantifier op2 vs2 f2')
              else Nothing
          (Quantifier q1 [] f1', Quantifier q2 [] f2') ->
              if q1 == q2 then zipFirstOrder q c p f1' f2' else Nothing
          (Connective l1 op1 r1, Connective l2 op2 r2) ->
              case (op1, op2) of
                (And, And) -> c (BinOp l1 (:&:) r1) (BinOp l2 (:&:) r2)
                (Or, Or) -> c (BinOp l1 (:|:) r1) (BinOp l2 (:|:) r2)
                (Imply, Imply) -> c (BinOp l1 (:=>:) r1) (BinOp l2 (:=>:) r2)
                (Equiv, Equiv) -> c (BinOp l1 (:<=>:) r1) (BinOp l2 (:<=>:) r2)
                _ -> Nothing
          (Equal _ _, Equal _ _) -> p f1 f2
          (Predicate _ _, Predicate _ _) -> p f1 f2
          _ -> Nothing
    atomic x@(Predicate _ _) = x
    atomic x@(Equal _ _) = x
    atomic _ = error "Chiou: atomic"

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f, Function f) => Term (CTerm v f) v f where
    foldTerm v fn t =
        case t of
          Variable x -> v x
          Function f ts -> fn f ts
    zipTerms  v f t1 t2 =
        case (t1, t2) of
          (Variable v1, Variable v2) -> v v1 v2
          (Function f1 ts1, Function f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    vt = Variable
    fApp f ts = Function f ts
    -- Yuck!  This can't be the right way...
    skolemConstant _ v = fromString (show (prettyVariable (prefix "c_" v)))
    skolemFunction _ v = fromString (show (prettyVariable (prefix "f_" v)))

data ConjunctiveNormalForm v p f =
    CNF [Sentence v p f]
    deriving (Eq)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [NormalTerm v f]
    | NFEqual (NormalTerm v f) (NormalTerm v f)
    deriving (Eq, Ord, Data, Typeable)

-- We need a distinct type here because of the functional dependencies
-- in class FirstOrderFormula.
data NormalTerm v f
    = NormalFunction f [NormalTerm v f]
    | NormalVariable v
    deriving (Eq, Ord, Data, Typeable)

instance Negatable (NormalSentence v p f) where
    (.~.) (NFNot (NFNot x)) = ((.~.) x)
    (.~.) (NFNot x)= x
    (.~.) x   = NFNot x
    negated (NFNot x) = not (negated x)
    negated _ = False

{-
instance (Arity p, Constants p, Combinable (NormalSentence v p f)) => Pred p (NormalTerm v f) (NormalSentence v p f) where
    pApp0 x = NFPredicate x []
    pApp1 x a = NFPredicate x [a]
    pApp2 x a b = NFPredicate x [a,b]
    pApp3 x a b c = NFPredicate x [a,b,c]
    pApp4 x a b c d = NFPredicate x [a,b,c,d]
    pApp5 x a b c d e = NFPredicate x [a,b,c,d,e]
    pApp6 x a b c d e f = NFPredicate x [a,b,c,d,e,f]
    pApp7 x a b c d e f g = NFPredicate x [a,b,c,d,e,f,g]
    x .=. y = NFEqual x y
    x .!=. y = NFNot (NFEqual x y)
-}

instance (Combinable (NormalSentence v p f), Term (NormalTerm v f) v f,
          IsString v, Show v,
          Ord p, IsString p, Constants p, Arity p, Data p, Show p,
          Ord f, IsString f, Show f) => FirstOrderFormula (NormalSentence v p f) (NormalSentence v p f) v where
    for_all _ _ = error "FirstOrderFormula NormalSentence"
    exists _ _ = error "FirstOrderFormula NormalSentence"
    foldFirstOrder _ c p f =
        case f of
          NFNot x -> c ((:~:) x)
          NFEqual _ _ -> p f
          NFPredicate _ _ -> p f
    zipFirstOrder _ c p f1 f2 =
        case (f1, f2) of
          (NFNot f1', NFNot f2') -> c ((:~:) f1') ((:~:) f2')
          (NFEqual _ _, NFEqual _ _) -> p f1 f2
          (NFPredicate _ _, NFPredicate _ _) -> p f1 f2
          _ -> Nothing
    atomic x@(NFPredicate _ _) = x
    atomic x@(NFEqual _ _) = x
    atomic _ = error "Chiou: atomic"

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f, Function f) => Term (NormalTerm v f) v f where
    vt = NormalVariable
    fApp = NormalFunction
    foldTerm v f t =
            case t of
              NormalVariable x -> v x
              NormalFunction x ts -> f x ts
    zipTerms v fn t1 t2 =
        case (t1, t2) of
          (NormalVariable x1, NormalVariable x2) -> v x1 x2
          (NormalFunction f1 ts1, NormalFunction f2 ts2) -> fn f1 ts1 f2 ts2
          _ -> Nothing
    skolemConstant _ v = fromString (show (prettyVariable (prefix "c_" v)))
    skolemFunction _ v = fromString (show (prettyVariable (prefix "f_" v)))

toSentence :: (FirstOrderFormula (Sentence v p f) (Sentence v p f) v, AtomEq (Sentence v p f) p (CTerm v f), Skolem f, Ord f, Data f, Data v, Function f, Constants p, Ord p) =>
              NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f, Function f) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = fApp f (map toTerm ts)
toTerm (NormalVariable v) = vt v

fromSentence :: forall v p f. (FirstOrderFormula (Sentence v p f) (Sentence v p f) v, PredicateEq p, Arity p, Constants p, Ord p, Ord f, Show p) =>
                Sentence v p f -> NormalSentence v p f
fromSentence = foldFirstOrder 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (foldAtomEq (\ p ts -> NFPredicate p (map fromTerm ts))
                             (\ t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2)))

fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
