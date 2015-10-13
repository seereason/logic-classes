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
import Data.Logic.Classes.Apply (HasPredicate(..), IsPredicate)
import Data.Logic.Classes.Arity (Arity(..))
import qualified Data.Logic.Classes.Atom as C
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(fromBool), asBool)
import Data.Logic.Classes.Equals (HasEquals(isEquals), HasEquality(..), showFirstOrderFormulaEq, substAtomEq, varAtomEq)
import Data.Logic.Classes.FirstOrder (fixityFirstOrder)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), Fixity(..), Associativity(..))
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

instance HasBoolean PredName where
    fromBool True = Named "true"
    fromBool False = Named "false"
    asBool x
        | x == fromBool True = Just True
        | x == fromBool False = Just False
        | True = Nothing

instance HasBoolean FOLEQ where
    fromBool x = R (fromBool x) []
    asBool (R p _)
        | fromBool True == p = Just True
        | fromBool False == p = Just False
        | True = Nothing
    asBool _ = Nothing

instance IsPredicate PredName

instance Pretty PredName where
    pPrint (:=:) = text "="
    pPrint (Named s) = text s

-- | Using PredName for the predicate type is not quite appropriate
-- here, but we need to implement this instance so we can use it as a
-- superclass of AtomEq below.
instance HasPredicate FOLEQ PredName TermType where
    foldPredicate f (EQUALS t1 t2) = f (:=:) [t1, t2]
    foldPredicate f (R p ts) = f (Named p) ts
    applyPredicate (Named p) ts = R p ts
    applyPredicate (:=:) [t1, t2] = EQUALS t1 t2
    applyPredicate (:=:) _ = error "arity"

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

instance C.IsFormula (Formula FOLEQ) FOLEQ => P.IsPropositional (Formula FOLEQ) FOLEQ where
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
    pPrint (EQUALS a b) = cat [pPrint a, pPrint (:=:), pPrint b]
    pPrint (R s ts) = cat ([pPrint s, pPrint "("] ++ intersperse (text ", ") (map pPrint ts) ++ [text ")"])

instance HasFixity (Formula FOLEQ) where
    fixity = fixityFirstOrder

instance C.IsFormula (Formula FOLEQ) FOLEQ => IsLiteral (Formula FOLEQ) FOLEQ where
    foldLiteral neg tf at lit =
        case lit of
          F -> tf False
          T -> tf True
          Atom a -> at a
          Not fm' -> neg fm'
          _ -> error "IsLiteral (Formula FOLEQ)"

-- instance PredicateEq PredName where
--     eqp = (:=:)

instance HasEquals PredName where
    isEquals (:=:) = True
    isEquals _ = False

instance HasEquality FOLEQ PredName TermType where
    foldEquals ap (EQUALS lhs rhs) = Just (ap lhs rhs)
    foldEquals _ _ = Nothing
    -- foldAtomEq pr _ (R p ts) = pr (Named p) ts
    -- foldAtomEq _ eq (EQUALS t1 t2) = eq t1 t2
    applyEquals = EQUALS
    -- applyEq' (Named s) ts = R s ts
    -- applyEq' (:=:) [t1, t2] = EQUALS t1 t2
    -- applyEq' _ _ = error "arity"

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
