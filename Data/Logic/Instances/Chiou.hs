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
import Data.List (intersperse)
import Data.Logic.Classes.Atom (Atom)
import Data.Monoid ((<>))
import Data.String (IsString(..))
import FOL ((.=.), foldEquate, HasEquate(..), HasPredicate(..), IsFunction, IsPredicate, IsQuantified(..),
            IsTerm(..), IsVariable, onatomsFirstOrder, overatomsFirstOrder, pApp, Quant(..))
import Formulas (HasBoolean(..), asBool, IsCombinable(..), BinOp(..), Combination(..), IsFormula(..), IsNegatable(..), (.~.))
import Lit (IsLiteral(foldLiteral))
import Pretty (Pretty(pPrint), HasFixity(..), text, rootFixity, Side(Unary))
import Prop (IsPropositional(..))
import Skolem (HasSkolem(..))

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

instance (Pretty v, Pretty f) => Pretty (CTerm v f) where
    pPrint (Variable v) = pPrint v
    pPrint (Function fn []) = pPrint fn
    pPrint (Function fn args) = pPrint fn <> text " [" <> mconcat (intersperse (text ", ") (map pPrint args)) <> text "]"

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

instance (Ord v, Ord p, Ord f) => IsNegatable (Sentence v p f) where
    naiveNegate = Not
    foldNegation' ne _ (Not x) = ne x
    -- foldNegation' ne other (Not x) = foldNegation' other ne x
    foldNegation' _ other x = other x

instance (HasBoolean p, Eq (Sentence v p f)) => HasBoolean (Sentence v p f) where
    fromBool x = Predicate (fromBool x) []
    asBool x
        | fromBool True == x = Just True
        | fromBool False == x = Just False
        | True = Nothing

instance ({- HasBoolean (Sentence v p f), -} Ord v, Ord p, Ord f) => IsCombinable (Sentence v p f) where
    foldCombination dj cj imp iff other fm =
        case fm of
          (Connective l Equiv r) -> l `iff` r
          (Connective l Imply r) -> l `imp` r
          (Connective l Or r) -> l `dj` r
          (Connective l And r) -> l `cj` r
          _ -> other fm
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y

instance (IsLiteral (Sentence  v p f) (Sentence  v p f), IsFunction f, IsVariable v, Ord p, HasBoolean p
         ) => IsFormula (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic x@(Predicate _ _) = x
    atomic x@(Equal _ _) = x
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder
    prettyFormula = error "FIXME: prettyFormula Sentence"

instance (IsFormula (Sentence v p f) (Sentence v p f), IsLiteral (Sentence v p f) (Sentence v p f),
          IsVariable v, IsFunction f, IsCombinable (Sentence v p f), HasBoolean p) =>
         IsPropositional (Sentence v p f) (Sentence v p f) where
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

instance (Ord p, HasBoolean p, IsVariable v, IsFunction f) => IsLiteral (Sentence v p f) (Sentence v p f) where
    foldLiteral ne _ _ (Not x) = ne x
    foldLiteral _ tf at (Predicate p ts) = maybe (at (Predicate p ts)) tf (asBool p)
    foldLiteral _ _ at (Equal t1 t2) = at (Equal t1 t2)
    foldLiteral _ _ _ _ = error "foldLiteral in IsLiteral (Sentence v p f) (Sentence v p f)"

data AtomicFunction v
    = AtomicFunction String
    -- This is redundant with the SkolemFunction and SkolemConstant
    -- constructors in the Chiou Term type.
    | AtomicSkolemFunction v
    deriving (Eq, Show)

instance IsString (AtomicFunction v) where
    fromString = AtomicFunction

instance IsVariable v => HasSkolem (AtomicFunction v) v where
    toSkolem = AtomicSkolemFunction
    fromSkolem (AtomicSkolemFunction v) = Just v
    fromSkolem _ = Nothing

-- The Atom type is not cleanly distinguished from the Sentence type, so we need an Atom instance for Sentence.
instance (IsVariable v, IsFunction f, IsPredicate p) => HasPredicate (Sentence v p f) p (CTerm v f) where
    foldPredicate ap (Predicate p ts) = ap p ts
    foldPredicate _ _ = error "FIXME: HasPredicate Sentence"
    applyPredicate = Predicate

instance (IsFunction f, IsVariable v, IsPredicate p) => HasEquate (Sentence v p f) p (CTerm v f) where
    foldEquate' ap (Equal t1 t2) = Just (ap t1 t2)
    foldEquate' _ _ = Nothing
    -- foldAtomEq ap _ (Predicate p ts) = ap p ts
    -- foldAtomEq _ eq (Equal t1 t2) = eq t1 t2
    -- foldAtomEq _ _ _ = error "Data.Logic.Instances.Chiou: Invalid atom"
    equate = Equal
    -- applyEq' = Predicate

instance (IsQuantified (Sentence v p f) (Sentence v p f) v, IsVariable v, IsFunction f) => Pretty (Sentence v p f) where
    pPrint = prettyFormula

instance (IsFormula (Sentence v p f) (Sentence v p f), IsFunction f, IsVariable v) => HasFixity (Sentence v p f) where
    fixity _ = rootFixity

instance (IsFormula (Sentence v p f) (Sentence v p f), IsLiteral (Sentence v p f) (Sentence v p f),
          IsVariable v, IsFunction f, Ord p, HasBoolean p) =>
          IsQuantified (Sentence v p f) (Sentence v p f) v where
    quant (:!:) v x = Quantifier ForAll [v] x
    quant (:?:) v x = Quantifier ExistsCh [v] x
    foldQuantified qu co tf at f =
        case f of
          Not x -> co ((:~:) x)
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> (:!:)
                          ExistsCh -> (:?:) in
              -- Use Logic.quant' here instead of the constructor
              -- Quantifier so as not to create quantifications with
              -- empty variable lists.
              qu op' v (quant' op' vs f')
          Quantifier _ [] f' -> foldQuantified qu co tf at f'
          Connective f1 Imply f2 -> co (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> co (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> co (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> co (BinOp f1 (:|:) f2)
          Predicate _ _ -> at f
          Equal _ _ -> at f

quant' :: IsQuantified formula atom v => Quant -> [v] -> formula -> formula
quant' op vs f = foldr (quant op) f vs

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

instance (IsVariable v, IsFunction f, Pretty (CTerm v f)) => IsTerm (CTerm v f) v f where
    foldTerm v fn t =
        case t of
          Variable x -> v x
          Function f ts -> fn f ts
    zipTerms  v f t1 t2 =
        case (t1, t2) of
          (Variable v1, Variable v2) -> Just (v v1 v2)
          (Function f1 ts1, Function f2 ts2) -> Just (f f1 ts1 f2 ts2)
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
-- in class IsQuantified.
data NormalTerm v f
    = NormalFunction f [NormalTerm v f]
    | NormalVariable v
    deriving (Eq, Ord, Data, Typeable)

instance (HasBoolean p, Eq (NormalSentence v p f)) => HasBoolean (NormalSentence v p f) where
    fromBool x = NFPredicate (fromBool x) []
    asBool x
        | fromBool True == x = Just True
        | fromBool False == x = Just False
        | True = Nothing

instance (Ord v, Ord p, Ord f) => IsNegatable (NormalSentence v p f) where
    naiveNegate = NFNot
    foldNegation' ne _ (NFNot x) = ne x
    -- foldNegation' ne other (NFNot x) = foldNegation' other ne x
    foldNegation' _ other x = other x

{-
instance (Arity p, HasBoolean p, IsCombinable (NormalSentence v p f)) => Pred p (NormalTerm v f) (NormalSentence v p f) where
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

instance (IsFormula (NormalSentence v p f) (NormalSentence v p f),
          IsVariable v, IsFunction f, IsCombinable (NormalSentence v p f)) => Pretty (NormalSentence v p f) where
    pPrint = prettyFormula

instance (IsPropositional (NormalSentence v p f) (NormalSentence v p f),
          IsFunction f, IsCombinable (NormalSentence v p f), IsVariable v, Pretty (NormalTerm v f), HasBoolean p) => IsFormula (NormalSentence v p f) (NormalSentence v p f) where
    atomic x@(NFPredicate _ _) = x
    atomic x@(NFEqual _ _) = x
    atomic _ = error "Chiou: atomic"
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder
    prettyFormula = error "FIXME"

instance (IsFormula (NormalSentence v p f) (NormalSentence v p f),
          IsCombinable (NormalSentence v p f), IsTerm (NormalTerm v f) v f,
          IsPropositional (NormalSentence v p f) (NormalSentence v p f),
          IsVariable v, IsFunction f, HasBoolean p) => IsQuantified (NormalSentence v p f) (NormalSentence v p f) v where
    quant _ _ _ = error "IsQuantified NormalSentence"
    foldQuantified _ co tf at f =
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

instance (IsFormula (NormalSentence v p f) (NormalSentence v p f),
          IsCombinable (NormalSentence v p f), IsFunction f, IsVariable v) => HasFixity (NormalSentence v p f) where
    fixity _ = rootFixity

instance (IsVariable v, IsFunction f, Pretty (NormalTerm v f)) => IsTerm (NormalTerm v f) v f where
    vt = NormalVariable
    fApp = NormalFunction
    foldTerm v f t =
            case t of
              NormalVariable x -> v x
              NormalFunction x ts -> f x ts
    zipTerms v fn t1 t2 =
        case (t1, t2) of
          (NormalVariable x1, NormalVariable x2) -> Just (v x1 x2)
          (NormalFunction f1 ts1, NormalFunction f2 ts2) -> Just (fn f1 ts1 f2 ts2)
          _ -> Nothing

toSentence :: (IsQuantified (Sentence v p f) (Sentence v p f) v, Atom (Sentence v p f) (CTerm v f) v,
               IsFunction f, IsVariable v, IsPredicate p) =>
              NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (IsVariable v, IsFunction f, Pretty (CTerm v f)) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = fApp f (map toTerm ts)
toTerm (NormalVariable v) = vt v

fromSentence :: forall v p f. (IsQuantified (Sentence v p f) (Sentence v p f) v, IsPredicate p, IsFunction f, HasBoolean p) =>
                Sentence v p f -> NormalSentence v p f
fromSentence = foldQuantified 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (\ x -> NFPredicate (fromBool x) [])
                 (\ a -> foldEquate (\ p ts -> NFPredicate p (map fromTerm ts)) (\ t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2)) a)

fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
