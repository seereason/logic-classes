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
import Data.Logic.Classes.Equals (PredicateEq(..), AtomEq(..), showFirstOrderFormulaEq)
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

-- | Using PredName for the predicate type is not quite appropriate
-- here, but we need to implement this instance so we can use it as a
-- superclass of AtomEq below.
instance Atom FOLEQ PredName TermType where
    foldAtom f (EQUALS t1 t2) = f (:=:) [t1, t2]
    foldAtom f (R p ts) = f (Named p) ts
    zipAtoms f (EQUALS t1 t2) (EQUALS t3 t4) = Just $ f (:=:) [t1, t2] (:=:) [t3, t4]
    zipAtoms f (R p1 ts1) (R p2 ts2) = Just $ f (Named p1) ts1 (Named p2) ts2
    zipAtoms _ _ _ = Nothing
    apply' (Named p) ts = R p ts
    apply' (:=:) [t1, t2] = EQUALS t1 t2
    apply' (:=:) _ = error "arity"

instance FirstOrderFormula (Formula FOLEQ) FOLEQ String where
    quant C.Exists v fm = Exists v fm
    quant C.Forall v fm = Forall v fm
    foldFirstOrder q c p fm =
        case fm of
          F -> c FALSE
          T -> c TRUE
          Atom a -> p a
          Not fm' -> c ((:~:) fm')
          And fm1 fm2 -> c (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> c (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> c (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> c (BinOp fm1 (:<=>:) fm2)
          Forall v fm' -> q C.Forall v fm'
          Exists v fm' -> q C.Exists v fm'
    zipFirstOrder qu co pr fm1 fm2 =
        foldFirstOrder qu' co' pr' fm1
        where
          qu' op v p = foldFirstOrder (\ op2 v2 p2 -> Just (qu op v p op2 v2 p2)) (\ _ -> Nothing) (\ _ -> Nothing) fm2
          co' c = foldFirstOrder (\ _ _ _ -> Nothing) (\ c2 -> Just (co c c2)) (\ _ -> Nothing) fm2
          pr' atom = foldFirstOrder (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ atom2 -> Just (pr atom atom2)) fm2
    atomic = Atom

instance PredicateEq PredName where
    eqp = (:=:)

instance AtomEq FOLEQ PredName TermType where
    foldAtomEq pr _ (R p ts) = pr (Named p) ts
    foldAtomEq _ eq (EQUALS t1 t2) = eq t1 t2
    zipAtomsEq pr _ (R p1 ts1) (R p2 ts2) = Just $ pr (Named p1) ts1 (Named p2) ts2
    zipAtomsEq _ eq (EQUALS t1 t2) (EQUALS t3 t4) = Just $ eq t1 t2 t3 t4
    zipAtomsEq _ _ _ _ = Nothing
    equals = EQUALS
