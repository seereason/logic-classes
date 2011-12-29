{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Types.Harrison.Equal where

-- ========================================================================= 
-- First order logic with equality.                                          
--                                                                           
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

import Data.Logic.Classes.Arity (Arity(..))
import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool), asBool)
import Data.Logic.Classes.Equals (AtomEq(..), showFirstOrderFormulaEq, PredicateEq(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import qualified Data.Logic.Classes.FirstOrder as C
import Data.Logic.Types.Harrison.FOL (TermType(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import Data.String (IsString(..))

data FOLEQ = EQUALS TermType TermType | R String [TermType] deriving (Eq, Ord, Show)
data PredName = (:=:) | Named String deriving (Eq, Ord, Show)

instance Arity PredName where
    arity (:=:) = Just 2
    arity _ = Nothing

instance Show (Formula FOLEQ) where
    show = showFirstOrderFormulaEq

instance IsString PredName where
    fromString "=" = (:=:)
    fromString s = Named s

instance Constants PredName where
    fromBool True = Named "true"
    fromBool False = Named "false"

-- | Using PredName for the predicate type is not quite appropriate
-- here, but we need to implement this instance so we can use it as a
-- superclass of AtomEq below.
instance Atom FOLEQ PredName TermType where
    foldAtom f _ (EQUALS t1 t2) = f (:=:) [t1, t2]
    foldAtom f tf (R p ts) = maybe (f (Named p) ts) tf (asBool (Named p))
    apply' (Named p) ts = R p ts
    apply' (:=:) [t1, t2] = EQUALS t1 t2
    apply' (:=:) _ = error "arity"

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

-- instance PredicateEq PredName where
--     eqp = (:=:)

instance AtomEq FOLEQ PredName TermType where
    foldAtomEq pr tf _ (R p ts) = maybe (pr (Named p) ts) tf (asBool (Named p))
    foldAtomEq _ _ eq (EQUALS t1 t2) = eq t1 t2
    equals = EQUALS
    applyEq' (Named s) ts = R s ts
    applyEq' (:=:) [t1, t2] = EQUALS t1 t2
    applyEq' _ _ = error "arity"

instance PredicateEq PredName where
    eqp = (:=:)
