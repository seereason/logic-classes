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
import Data.Logic.Classes.Boolean (Boolean(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..), quant')
import Data.Logic.Classes.Logic (Logic(..))
import Data.Logic.Classes.Negatable (Negatable(..))
import Data.Logic.Classes.Pred (Pred(..), pApp)
import Data.Logic.Classes.Term as Logic
import qualified Data.Logic.Classes.FirstOrder as L
import Data.Logic.Classes.Propositional (PropositionalFormula(..), BinOp(..), Combine(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Variable (Variable)
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

instance (Ord v, Ord p, Ord f) => Logic (Sentence v p f) where
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y

instance (Ord v, IsString v, Data v, Variable v, 
          Ord p, IsString p, Data p, Boolean p, Arity p,
          Ord f, IsString f, Data f, Skolem f, 
          Boolean (Sentence v p f), Logic (Sentence v p f)) =>
         PropositionalFormula (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Predicate p ts) = pApp p ts
    atomic (Equal t1 t2) = t1 .=. t2
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

instance (Ord v, Ord p, Arity p, Boolean p, Ord f) => Pred p (CTerm v f) (Sentence v p f) where
    pApp0 x = Predicate x []
    pApp1 x a = Predicate x [a]
    pApp2 x a b = Predicate x [a,b]
    pApp3 x a b c = Predicate x [a,b,c]
    pApp4 x a b c d = Predicate x [a,b,c,d]
    pApp5 x a b c d e = Predicate x [a,b,c,d,e]
    pApp6 x a b c d e f = Predicate x [a,b,c,d,e,f]
    pApp7 x a b c d e f g = Predicate x [a,b,c,d,e,f,g]
    -- fApp (AtomicSkolemFunction n) [] = SkolemConstant n
    -- fApp (AtomicSkolemFunction n) ts = SkolemFunction n ts
    x .=. y = Equal x y

instance (Ord v, IsString v, Variable v, Data v, Show v,
          Ord p, IsString p, Boolean p, Arity p, Data p, Show p,
          Ord f, IsString f, Skolem f, Data f, Show f,
          PropositionalFormula (Sentence v p f) (Sentence v p f)) =>
          FirstOrderFormula (Sentence v p f) (CTerm v f) v p f where
    for_all v x = Quantifier ForAll [v] x
    exists v x = Quantifier ExistsCh [v] x
    foldFirstOrder q c p f =
        case f of
          Not x -> c ((:~:) x)
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> All
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
          Predicate name ts -> p (L.Apply name ts)
          Equal t1 t2 -> p (L.Equal t1 t2)
    zipFirstOrder q c p f1 f2 =
        case (f1, f2) of
          (Not f1', Not f2') -> c ((:~:) f1') ((:~:) f2')
          (Quantifier op1 (v1:vs1) f1', Quantifier op2 (v2:vs2) f2') ->
              if op1 == op2
              then let op' = case op1 of
                               ForAll -> All
                               ExistsCh -> Exists in
                   q op' v1 (Quantifier op1 vs1 f1') All v2 (Quantifier op2 vs2 f2')
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
          (Equal l1 r1, Equal l2 r2) -> p (L.Equal l1 r1) (L.Equal l2 r2)
          (Predicate p1 ts1, Predicate p2 ts2) -> p (L.Apply p1 ts1) (L.Apply p2 ts2)
          _ -> Nothing

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f) => Logic.Term (CTerm v f) v f where
    foldTerm v fn t =
        case t of
          Variable x -> v x
          Function f ts -> fn f ts
    zipT  v f t1 t2 =
        case (t1, t2) of
          (Variable v1, Variable v2) -> v v1 v2
          (Function f1 ts1, Function f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Variable
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

instance Negatable (NormalSentence v p f) where
    (.~.) (NFNot (NFNot x)) = ((.~.) x)
    (.~.) (NFNot x)= x
    (.~.) x   = NFNot x
    negated (NFNot x) = not (negated x)
    negated _ = False

instance (Arity p, Boolean p, Logic (NormalSentence v p f)) => Pred p (NormalTerm v f) (NormalSentence v p f) where
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

instance (Logic (NormalSentence v p f), Logic.Term (NormalTerm v f) v f,
          IsString v, Show v,
          Ord p, IsString p, Boolean p, Arity p, Data p, Show p,
          Ord f, IsString f, Show f) => FirstOrderFormula (NormalSentence v p f) (NormalTerm v f) v p f where
    for_all _ _ = error "FirstOrderFormula NormalSentence"
    exists _ _ = error "FirstOrderFormula NormalSentence"
    foldFirstOrder _ c p f =
        case f of
          NFNot x -> c ((:~:) x)
          NFEqual t1 t2 -> p (L.Equal t1 t2)
          NFPredicate pr ts -> p (L.Apply pr ts)
    zipFirstOrder _ c p f1 f2 =
        case (f1, f2) of
          (NFNot f1', NFNot f2') -> c ((:~:) f1') ((:~:) f2')
          (NFEqual f1l f1r, NFEqual f2l f2r) -> p (L.Equal f1l f1r) (L.Equal f2l f2r)
          (NFPredicate p1 ts1, NFPredicate p2 ts2) -> p (L.Apply p1 ts1) (L.Apply p2 ts2)
          _ -> Nothing

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f) => Logic.Term (NormalTerm v f) v f where
    var = NormalVariable
    fApp = NormalFunction
    foldTerm v f t =
            case t of
              NormalVariable x -> v x
              NormalFunction x ts -> f x ts
    zipT v fn t1 t2 =
        case (t1, t2) of
          (NormalVariable x1, NormalVariable x2) -> v x1 x2
          (NormalFunction f1 ts1, NormalFunction f2 ts2) -> fn f1 ts1 f2 ts2
          _ -> Nothing

toSentence :: FirstOrderFormula (Sentence v p f) (CTerm v f) v p f => NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = Logic.fApp f (map toTerm ts)
toTerm (NormalVariable v) = Logic.var v

fromSentence :: forall v p f. FirstOrderFormula (Sentence v p f) (CTerm v f) v p f =>
                Sentence v p f -> NormalSentence v p f
fromSentence = foldFirstOrder 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (\ pa ->
                      case pa of
                        L.Equal t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2)
                        L.NotEqual t1 t2 -> NFNot (NFEqual (fromTerm t1) (fromTerm t2))
                        L.Constant x -> NFPredicate (fromBool x) []
                        L.Apply p ts -> NFPredicate p (map fromTerm ts))


fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
