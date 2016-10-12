{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, GADTs, MultiParamTypeClasses,
             RankNTypes, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
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
import Data.Logic.ATP.Apply (HasApply(..), IsPredicate, pApp)
import Data.Logic.ATP.Equate ((.=.), HasEquate(..), overtermsEq, ontermsEq)
import Data.Logic.ATP.Formulas (asBool, IsAtom, IsFormula(..))
import Data.Logic.ATP.Lit ((.~.), associativityLiteral, convertToLiteral, IsLiteral(..), JustLiteral,
                           onatomsLiteral, overatomsLiteral, precedenceLiteral, prettyLiteral, showLiteral)
import Data.Logic.ATP.Pretty (Associativity(..), HasFixity(..), Side(Top), text)
import Data.Logic.ATP.Prop (BinOp(..), IsPropositional(..))
import Data.Logic.ATP.Quantified (associativityQuantified, IsQuantified(..), onatomsQuantified, overatomsQuantified,
                                  precedenceQuantified, prettyQuantified, Quant(..), showQuantified)
import Data.Logic.ATP.Skolem (HasSkolem(..), prettySkolem)
import Data.Logic.ATP.Term (associativityTerm, IsFunction, IsTerm(..), IsVariable, precedenceTerm, prettyTerm, showTerm)
import Data.Logic.Classes.Atom (Atom)
import Data.Set as Set (notMember)
import Data.String (IsString(..))
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint, pPrintPrec))

data Sentence v p f
    = Connective (Sentence v p f) Connective (Sentence v p f)
    | Quantifier Quantifier [v] (Sentence v p f)
    | Not (Sentence v p f)
    | Predicate p [CTerm v f]
    | Equal (CTerm v f) (CTerm v f)
    | TT | FF
    deriving (Eq, Ord, Data, Typeable)

data CTerm v f
    = Function f [CTerm v f]
    | Variable v
    deriving (Eq, Ord, Data, Typeable)

instance IsString v => IsString (CTerm v f) where
    fromString = Variable . fromString

instance (IsVariable v, IsFunction f) => Show (CTerm v f) where
    show = showTerm

instance HasFixity (CTerm v f) where
    precedence _ = 0
    associativity _ = InfixN

instance (IsVariable v, Pretty v, IsFunction f, Pretty f) => Pretty (CTerm v f) where
    pPrintPrec = prettyTerm

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

{-
instance (Eq (Sentence v p f)) => HasBoolean (Sentence v p f) where
    fromBool x = Predicate (fromBool x) []
    asBool x
        | fromBool True == x = Just True
        | fromBool False == x = Just False
        | True = Nothing
-}

instance (IsPredicate p, IsLiteral (Sentence  v p f),
          IsFunction f, IsVariable v, Ord p) => IsFormula (Sentence v p f) where
    type AtomOf (Sentence v p f) = Sentence  v p f
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic TT = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic FF = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic x@(Predicate _ _) = x
    atomic x@(Equal _ _) = x
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified
    asBool TT = Just True
    asBool FF = Just False
    asBool _ = Nothing
    true = TT
    false = FF

instance (IsPredicate p,  IsPropositional (Sentence v p f),
          IsVariable v, IsFunction f) => IsPropositional (Sentence v p f) where
    foldPropositional' ho co ne tf at formula =
        case formula of
          Not x -> ne x
          TT -> tf True
          FF -> tf False
          Connective f1 Imply f2 -> co f1 (:=>:) f2
          Connective f1 Equiv f2 -> co f1 (:<=>:) f2
          Connective f1 And f2 -> co f1 (:&:) f2
          Connective f1 Or f2 -> co f1 (:|:) f2
          Predicate p ts -> at (Predicate p ts)
          Equal t1 t2 -> at (Equal t1 t2)
          _ -> ho formula
    foldCombination other dj cj imp iff fm =
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

instance (IsVariable v, IsPredicate p, IsFunction f) => IsAtom (Sentence v p f)

instance (IsVariable v, IsPredicate p, IsFunction f) => Show (Sentence v p f) where
    showsPrec = showQuantified Top

instance (IsVariable v, IsPredicate p, IsFunction f) => IsLiteral (Sentence v p f) where
    foldLiteral' _ ne _ _ (Not x) = ne x
    foldLiteral' _ _ tf _ TT = tf True
    foldLiteral' _ _ tf _ FF = tf False
    foldLiteral' _ _ _ at (Predicate p ts) = at (Predicate p ts)
    foldLiteral' _ _ _ at (Equal t1 t2) = at (Equal t1 t2)
    foldLiteral' ho _ _ _ fm = ho fm
    naiveNegate = Not
    foldNegation _ ne (Not x) = ne x
    foldNegation other _ x = other x

data AtomicFunction v
    = AtomicFunction String
    -- This is redundant with the SkolemFunction and SkolemConstant
    -- constructors in the Chiou Term type.
    | AtomicSkolemFunction v Int
    deriving (Eq, Ord, Show)

instance IsVariable v => IsString (AtomicFunction v) where
    fromString = AtomicFunction

instance IsVariable v => IsFunction (AtomicFunction v) where

instance IsVariable v => Pretty (AtomicFunction v) where
    pPrint = prettySkolem (\(AtomicFunction s) -> text s)

instance IsVariable v => HasSkolem (AtomicFunction v) where
    type SVarOf (AtomicFunction v) = v
    toSkolem = AtomicSkolemFunction
    foldSkolem _ sk (AtomicSkolemFunction v n) = sk v n
    foldSkolem f _ af = f af
    variantSkolem f fns | Set.notMember f fns = f
    variantSkolem (AtomicFunction s) fns = variantSkolem (AtomicFunction (s ++ "'")) fns
    variantSkolem (AtomicSkolemFunction v n) fns = variantSkolem (AtomicSkolemFunction v (succ n)) fns

-- The Atom type is not cleanly distinguished from the Sentence type, so we need an Atom instance for Sentence.
instance (IsVariable v, IsFunction f, IsPredicate p) => HasApply (Sentence v p f) where
    type PredOf (Sentence v p f) = p
    type TermOf (Sentence v p f) = CTerm v f
    foldApply' _ ap (Predicate p ts) = ap p ts
    foldApply' d _ p = d p
    applyPredicate = Predicate
    overterms = overtermsEq
    onterms = ontermsEq

instance (IsFunction f, IsVariable v, IsPredicate p) => HasEquate (Sentence v p f) where
    foldEquate eq _ (Equal t1 t2) = eq t1 t2
    foldEquate _ ap (Predicate p ts) = ap p ts
    foldEquate _ _ _ = error "IsAtomWithEquate Sentence"
    equate = Equal
    -- applyEq' = Predicate

instance (IsQuantified (Sentence v p f), IsVariable v, IsFunction f) => Pretty (Sentence v p f) where
    pPrintPrec = prettyQuantified Top

instance (IsFormula (Sentence v p f), IsVariable v, IsPredicate p, IsFunction f) => HasFixity (Sentence v p f) where
    precedence = precedenceQuantified
    associativity = associativityQuantified

instance (IsPredicate p, IsFormula (Sentence v p f), IsLiteral (Sentence v p f), IsVariable v, IsFunction f, Ord p
         ) => IsQuantified (Sentence v p f) where
    type (VarOf (Sentence v p f)) = v
    quant (:!:) v x = Quantifier ForAll [v] x
    quant (:?:) v x = Quantifier ExistsCh [v] x
    foldQuantified qu co ne tf at f =
        case f of
          Not x -> ne x
          TT -> tf True
          FF -> tf False
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> (:!:)
                          ExistsCh -> (:?:) in
              -- Use Logic.quant' here instead of the constructor
              -- Quantifier so as not to create quantifications with
              -- empty variable lists.
              qu op' v (quant' op' vs f')
          Quantifier _ [] f' -> foldQuantified qu co ne tf at f'
          Connective f1 Imply f2 -> co f1 (:=>:) f2
          Connective f1 Equiv f2 -> co f1 (:<=>:) f2
          Connective f1 And f2 -> co f1 (:&:) f2
          Connective f1 Or f2 -> co f1 (:|:) f2
          Predicate _ _ -> at f
          Equal _ _ -> at f

quant' :: IsQuantified formula => Quant -> [VarOf formula] -> formula -> formula
quant' op vs f = foldr (quant op) f vs

instance (IsVariable v, IsFunction f, Pretty (CTerm v f)) => IsTerm (CTerm v f) where
    type TVarOf (CTerm v f) = v
    type FunOf (CTerm v f) = f
    foldTerm v fn t =
        case t of
          Variable x -> v x
          Function f ts -> fn f ts
    vt = Variable
    fApp f ts = Function f ts

data ConjunctiveNormalForm v p f =
    CNF [Sentence v p f]
    deriving (Eq)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [NormalTerm v f]
    | NFEqual (NormalTerm v f) (NormalTerm v f)
    | NFTT
    | NFFF
    deriving (Eq, Ord, Data, Typeable)

-- We need a distinct type here because of the functional dependencies
-- in class IsQuantified.
data NormalTerm v f
    = NormalFunction f [NormalTerm v f]
    | NormalVariable v
    deriving (Eq, Ord, Data, Typeable)

instance (IsVariable v, IsPredicate p, IsFunction f) => Show (NormalSentence v p f) where
    show = showLiteral

instance (IsVariable v, IsPredicate p, IsFunction f) => IsAtom (NormalSentence v p f)

instance (IsVariable v, IsPredicate p, IsFunction f) => JustLiteral (NormalSentence v p f)

instance (IsVariable v, IsPredicate p, IsFunction f) => IsLiteral (NormalSentence v p f) where
    foldLiteral' _ho ne tf at fm =
        case fm of
          NFNot s -> ne s
          NFTT -> tf True
          NFFF -> tf False
          NFPredicate _p _ts -> at fm
          NFEqual _t1 _t2 -> at fm
    naiveNegate = NFNot
    foldNegation _ ne (NFNot x) = ne x
    -- foldNegation' ne other (NFNot x) = foldNegation' other ne x
    foldNegation other _ x = other x


instance (IsLiteral (NormalSentence v p f),
          IsVariable v, IsPredicate p, IsFunction f
         ) => Pretty (NormalSentence v p f) where
    pPrintPrec = prettyLiteral

instance (Pretty (NormalTerm v f),
          IsVariable v, IsPredicate p, IsFunction f
         ) => IsFormula (NormalSentence v p f) where
    type (AtomOf (NormalSentence v p f)) = NormalSentence v p f
    atomic x@(NFPredicate _ _) = x
    atomic x@(NFEqual _ _) = x
    atomic _ = error "Chiou: atomic"
    overatoms = overatomsLiteral
    onatoms = onatomsLiteral
    true = NFTT
    false = NFFF
    asBool NFTT = Just True
    asBool NFFF = Just False
    asBool _ = Nothing

instance (IsVariable v, IsPredicate p, IsFunction f) => HasFixity (NormalSentence v p f) where
    precedence = precedenceLiteral
    associativity = associativityLiteral

instance IsVariable v => IsString (NormalTerm v f) where
    fromString = NormalVariable . fromString

instance (IsFunction f, IsVariable v) => HasFixity (NormalTerm v f) where
    precedence = precedenceTerm
    associativity = associativityTerm

instance (IsVariable v, IsFunction f, Pretty (NormalTerm v f)) => IsTerm (NormalTerm v f) where
    type TVarOf (NormalTerm v f) = v
    type FunOf (NormalTerm v f) = f
    vt = NormalVariable
    fApp = NormalFunction
    foldTerm v f t =
            case t of
              NormalVariable x -> v x
              NormalFunction x ts -> f x ts

instance (IsVariable v, IsFunction f) => Pretty (NormalTerm v f) where
    pPrintPrec = prettyTerm

instance (IsVariable v, IsFunction f) => Show (NormalTerm v f) where
    show = showTerm

toSentence :: (IsQuantified (Sentence v p f),
               Atom (Sentence v p f) (CTerm v f) v,
               IsFunction f, IsVariable v, IsPredicate p
              ) => NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence NFTT = true
toSentence NFFF = false
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (IsVariable v, IsFunction f, Pretty (CTerm v f)) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = fApp f (map toTerm ts)
toTerm (NormalVariable v) = vt v

fromSentence :: forall v p f fof atom.
                (IsVariable v, IsPredicate p, IsFunction f,
                 fof ~ Sentence v p f,
                 atom ~ Sentence v p f,
                 IsQuantified fof
                ) => Sentence v p f -> NormalSentence v p f
fromSentence = convertToLiteral (error "fromSentence failure")
                                (foldEquate (\ t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2))
                                            (\ p ts -> NFPredicate p (map fromTerm ts)))
{-
fromSentence = convertQuantified (foldEquate (\ p ts -> applyPredicate p (map fromTerm ts))
                                             (\ t1 t2 -> equate (fromTerm t1) (fromTerm t2))) id
fromSentence = foldQuantified 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (\ x -> NFPredicate (fromBool x) [])
                 (\ a -> foldEquate (\ p ts -> NFPredicate p (map fromTerm ts)) (\ t1 t2 -> NFEqual (fromTerm t1) (fromTerm t2)) a)
-}
fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
