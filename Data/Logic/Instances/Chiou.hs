{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-orphans -fno-warn-missing-signatures #-}
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
import Data.Logic.Classes.Apply (Apply(..), Predicate)
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Combine (Combinable(..), BinOp(..), Combination(..))
import Data.Logic.Classes.Constants (Constants(..), asBool, true, false)
import Data.Logic.Classes.Equals (AtomEq(..), (.=.))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..), quant', pApp, prettyFirstOrder, fixityFirstOrder, foldAtomsFirstOrder, mapAtomsFirstOrder)
import Data.Logic.Classes.Formula (Formula(..))
import Data.Logic.Classes.Negate (Negatable(..), (.~.))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity(..))
import Data.Logic.Classes.Term (Term(..), Function)
import Data.Logic.Classes.Variable (Variable)
import qualified Data.Logic.Classes.FirstOrder as L
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.Logic.Classes.Skolem (Skolem(..))
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
    negatePrivate = Not
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (Constants p, Eq (Sentence v p f)) => Constants (Sentence v p f) where
    fromBool x = Predicate (fromBool x) []
    asBool x
        | fromBool True == x = Just True
        | fromBool False == x = Just False
        | True = Nothing

instance ({- Constants (Sentence v p f), -} Ord v, Ord p, Ord f) => Combinable (Sentence v p f) where
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y

instance (Predicate p, Function f v) => Formula (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic x@(Predicate _ _) = x
    atomic x@(Equal _ _) = x
    foldAtoms = foldAtomsFirstOrder
    mapAtoms = mapAtomsFirstOrder

instance (Formula (Sentence v p f) (Sentence v p f), Variable v, Predicate p, Function f v, Combinable (Sentence v p f)) =>
         PropositionalFormula (Sentence v p f) (Sentence v p f) where
    foldPropositional co tf at formula =
        case formula of
          Not x -> co ((:~:) x)
          Quantifier _ _ _ -> error "Logic.Instance.Chiou.foldF0: unexpected"
          Connective f1 Imply f2 -> co (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> co (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> co (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> co (BinOp f1 (:|:) f2)
          Predicate p ts -> maybe (at (Predicate p ts)) tf (asBool p)
          Equal t1 t2 -> at (Equal t1 t2)

data AtomicFunction v
    = AtomicFunction String
    -- This is redundant with the SkolemFunction and SkolemConstant
    -- constructors in the Chiou Term type.
    | AtomicSkolemFunction v
    deriving (Eq, Show)

instance IsString (AtomicFunction v) where
    fromString = AtomicFunction

instance Variable v => Skolem (AtomicFunction v) v where
    toSkolem = AtomicSkolemFunction
    isSkolem (AtomicSkolemFunction _) = True
    isSkolem _ = False

-- The Atom type is not cleanly distinguished from the Sentence type, so we need an Atom instance for Sentence.
instance (Variable v, Predicate p, Function f v) => Apply (Sentence v p f) p (CTerm v f) where
    foldApply ap tf (Predicate p ts) = maybe (ap p ts) tf (asBool p)
    foldApply _ _ _ = error "Data.Logic.Instances.Chiou: Invalid atom"
    apply' = Predicate

instance Predicate p => AtomEq (Sentence v p f) p (CTerm v f) where
    foldAtomEq ap tf _ (Predicate p ts) = if p == true then tf True else if p == false then tf False else ap p ts
    foldAtomEq _ _ eq (Equal t1 t2) = eq t1 t2
    foldAtomEq _ _ _ _ = error "Data.Logic.Instances.Chiou: Invalid atom"
    equals = Equal
    applyEq' = Predicate

instance (FirstOrderFormula (Sentence v p f) (Sentence v p f) v, Variable v, Predicate p, Function f v) => Pretty (Sentence v p f) where
    pretty = prettyFirstOrder (\ _ a -> pretty a) pretty 0

instance (Formula (Sentence v p f) (Sentence v p f), Predicate p, Function f v, Variable v) => HasFixity (Sentence v p f) where
    fixity = fixityFirstOrder

instance (Formula (Sentence v p f) (Sentence v p f),
          Variable v, Predicate p, Function f v) =>
          FirstOrderFormula (Sentence v p f) (Sentence v p f) v where
    for_all v x = Quantifier ForAll [v] x
    exists v x = Quantifier ExistsCh [v] x
    foldFirstOrder qu co tf at f =
        case f of
          Not x -> co ((:~:) x)
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> Forall
                          ExistsCh -> Exists in
              -- Use Logic.quant' here instead of the constructor
              -- Quantifier so as not to create quantifications with
              -- empty variable lists.
              qu op' v (quant' op' vs f')
          Quantifier _ [] f' -> foldFirstOrder qu co tf at f'
          Connective f1 Imply f2 -> co (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> co (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> co (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> co (BinOp f1 (:|:) f2)
          Predicate _ _ -> at f
          Equal _ _ -> at f
{-
    zipFirstOrder qu co tf at f1 f2 =
        case (f1, f2) of
          (Not f1', Not f2') -> co ((:~:) f1') ((:~:) f2')
          (Quantifier op1 (v1:vs1) f1', Quantifier op2 (v2:vs2) f2') ->
              if op1 == op2
              then let op' = case op1 of
                               ForAll -> Forall
                               ExistsCh -> Exists in
                   qu op' v1 (Quantifier op1 vs1 f1') Forall v2 (Quantifier op2 vs2 f2')
              else Nothing
          (Quantifier q1 [] f1', Quantifier q2 [] f2') ->
              if q1 == q2 then zipFirstOrder qu co tf at f1' f2' else Nothing
          (Connective l1 op1 r1, Connective l2 op2 r2) ->
              case (op1, op2) of
                (And, And) -> co (BinOp l1 (:&:) r1) (BinOp l2 (:&:) r2)
                (Or, Or) -> co (BinOp l1 (:|:) r1) (BinOp l2 (:|:) r2)
                (Imply, Imply) -> co (BinOp l1 (:=>:) r1) (BinOp l2 (:=>:) r2)
                (Equiv, Equiv) -> co (BinOp l1 (:<=>:) r1) (BinOp l2 (:<=>:) r2)
                _ -> Nothing
          (Equal _ _, Equal _ _) -> at f1 f2
          (Predicate _ _, Predicate _ _) -> at f1 f2
          _ -> Nothing
-}

instance (Variable v, Function f v) => Term (CTerm v f) v f where
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

instance (Constants p, Eq (NormalSentence v p f)) => Constants (NormalSentence v p f) where
    fromBool x = NFPredicate (fromBool x) []
    asBool x
        | fromBool True == x = Just True
        | fromBool False == x = Just False
        | True = Nothing

instance Negatable (NormalSentence v p f) where
    negatePrivate = NFNot
    foldNegation normal inverted (NFNot x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

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

instance (Formula (NormalSentence v p f) (NormalSentence v p f),
          Variable v, Predicate p, Function f v, Combinable (NormalSentence v p f)) => Pretty (NormalSentence v p f) where
    pretty = prettyFirstOrder (\ _ a -> pretty a) pretty 0

instance (Predicate p, Function f v, Combinable (NormalSentence v p f)) => Formula (NormalSentence v p f) (NormalSentence v p f) where
    atomic x@(NFPredicate _ _) = x
    atomic x@(NFEqual _ _) = x
    atomic _ = error "Chiou: atomic"
    foldAtoms = foldAtomsFirstOrder
    mapAtoms = mapAtomsFirstOrder

instance (Formula (NormalSentence v p f) (NormalSentence v p f), Combinable (NormalSentence v p f), Term (NormalTerm v f) v f,
          Variable v, Predicate p, Function f v) => FirstOrderFormula (NormalSentence v p f) (NormalSentence v p f) v where
    for_all _ _ = error "FirstOrderFormula NormalSentence"
    exists _ _ = error "FirstOrderFormula NormalSentence"
    foldFirstOrder _ co tf at f =
        case f of
          NFNot x -> co ((:~:) x)
          NFEqual _ _ -> at f
          NFPredicate p _ -> maybe (at f) tf (asBool p)
{-
    zipFirstOrder _ co tf at f1 f2 =
        case (f1, f2) of
          (NFNot f1', NFNot f2') -> co ((:~:) f1') ((:~:) f2')
          (NFEqual _ _, NFEqual _ _) -> at f1 f2
          (NFPredicate _ _, NFPredicate _ _) -> at f1 f2
          _ -> Nothing
-}

instance (Formula (NormalSentence v p f) (NormalSentence v p f),
          Combinable (NormalSentence v p f), Predicate p, Function f v, Variable v) => HasFixity (NormalSentence v p f) where
    fixity = fixityFirstOrder

instance (Variable v, Function f v) => Term (NormalTerm v f) v f where
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

toSentence :: (FirstOrderFormula (Sentence v p f) (Sentence v p f) v, Atom (Sentence v p f) (CTerm v f) v, Function f v, Variable v, Predicate p) =>
              NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (Variable v, Function f v) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = fApp f (map toTerm ts)
toTerm (NormalVariable v) = vt v

fromSentence :: forall v p f. (FirstOrderFormula (Sentence v p f) (Sentence v p f) v, Predicate p) =>
                Sentence v p f -> NormalSentence v p f
fromSentence = foldFirstOrder 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (\ x -> NFPredicate (fromBool x) [])
                 (foldAtomEq (\ p ts -> NFPredicate p (map fromTerm ts))
                             (\ x -> NFPredicate (fromBool x) [])
                             (\ t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2)))

fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
