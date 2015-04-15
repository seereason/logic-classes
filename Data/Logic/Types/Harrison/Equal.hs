{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Types.Harrison.Equal where

-- =========================================================================
-- First order logic with equality.
--
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
-- =========================================================================

import Data.Generics (Data, Typeable)
import Data.List (intersperse)
import Data.Logic.Classes.Apply (Apply(..), Predicate)
import Data.Logic.Classes.Arity (Arity(..))
import qualified Data.Logic.Classes.Atom as C
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool), asBool)
import Data.Logic.Classes.Equals (AtomEq(..), showFirstOrderFormulaEq, substAtomEq, varAtomEq)
import Data.Logic.Classes.FirstOrder (fixityFirstOrder, mapAtomsFirstOrder, foldAtomsFirstOrder)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity(..), Fixity(..), FixityDirection(..))
import qualified Data.Logic.Classes.Propositional as P
import Data.Logic.Harrison.Resolution (matchAtomsEq)
import Data.Logic.Harrison.Tableaux (unifyAtomsEq)
import Data.Logic.Resolution (isRenameOfAtomEq, getSubstAtomEq)
import Data.Logic.Types.Harrison.FOL (TermType(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import Data.String (IsString(..))
import Text.PrettyPrint (text, cat)

data FOLEQ = EQUALS TermType TermType | R String [TermType] deriving (Eq, Ord, Show)
data PredName = (:=:) | Named String deriving (Eq, Ord, Show, Data, Typeable)

instance Arity PredName where
    arity (:=:) = Just 2
    arity _ = Nothing

instance Show (Formula FOLEQ) where
    show = showFirstOrderFormulaEq

instance HasFixity FOLEQ where
    fixity (EQUALS _ _) = Fixity 5 InfixL
    fixity _ = Fixity 10 InfixN

instance IsString PredName where
    fromString "=" = (:=:)
    fromString s = Named s

instance Constants PredName where
    fromBool True = Named "true"
    fromBool False = Named "false"
    asBool x
        | x == fromBool True = Just True
        | x == fromBool False = Just False
        | True = Nothing

instance Constants FOLEQ where
    fromBool x = R (fromBool x) []
    asBool (R p _)
        | fromBool True == p = Just True
        | fromBool False == p = Just False
        | True = Nothing
    asBool _ = Nothing

instance Predicate PredName

instance Pretty PredName where
    pretty (:=:) = text "="
    pretty (Named s) = text s

-- | Using PredName for the predicate type is not quite appropriate
-- here, but we need to implement this instance so we can use it as a
-- superclass of AtomEq below.
instance Apply FOLEQ PredName TermType where
    foldApply f _ (EQUALS t1 t2) = f (:=:) [t1, t2]
    foldApply f tf (R p ts) = maybe (f (Named p) ts) tf (asBool (Named p))
    apply' (Named p) ts = R p ts
    apply' (:=:) [t1, t2] = EQUALS t1 t2
    apply' (:=:) _ = error "arity"

{-
instance FirstOrderFormula (Formula FOLEQ) FOLEQ String where
    exists = Exists
    for_all = Forall
    foldFirstOrder qu co tf at fm =
        case fm of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not fm' -> co ((:~:) fm')
          And fm1 fm2 -> co (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> co (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> co (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> co (BinOp fm1 (:<=>:) fm2)
          Forall v fm' -> qu C.Forall v fm'
          Exists v fm' -> qu C.Exists v fm'
    atomic = Atom
-}

instance C.Formula (Formula FOLEQ) FOLEQ => P.PropositionalFormula (Formula FOLEQ) FOLEQ where
    foldPropositional co tf at fm =
        case fm of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not fm' -> co ((:~:) fm')
          And fm1 fm2 -> co (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> co (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> co (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> co (BinOp fm1 (:<=>:) fm2)
          Forall _ _ -> error "quantifier in propositional formula"
          Exists _ _ -> error "quantifier in propositional formula"

instance Pretty FOLEQ where
    pretty (EQUALS a b) = cat [pretty a, pretty (:=:), pretty b]
    pretty (R s ts) = cat ([pretty s, pretty "("] ++ intersperse (text ", ") (map pretty ts) ++ [text ")"])

instance HasFixity (Formula FOLEQ) where
    fixity = fixityFirstOrder

instance C.Formula (Formula FOLEQ) FOLEQ => Literal (Formula FOLEQ) FOLEQ where
    foldLiteral neg tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not fm' -> neg fm'
          _ -> error "Literal (Formula FOLEQ)"

-- instance PredicateEq PredName where
--     eqp = (:=:)

instance AtomEq FOLEQ PredName TermType where
    foldAtomEq pr tf _ (R p ts) = maybe (pr (Named p) ts) tf (asBool (Named p))
    foldAtomEq _ _ eq (EQUALS t1 t2) = eq t1 t2
    equals = EQUALS
    applyEq' (Named s) ts = R s ts
    applyEq' (:=:) [t1, t2] = EQUALS t1 t2
    applyEq' _ _ = error "arity"

instance C.Atom FOLEQ TermType String where
    substitute = substAtomEq
    freeVariables = varAtomEq
    allVariables = varAtomEq
    unify = unifyAtomsEq
    match = matchAtomsEq
    foldTerms f r (R _ ts) = foldr f r ts
    foldTerms f r (EQUALS t1 t2) = f t2 (f t1 r)
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq
