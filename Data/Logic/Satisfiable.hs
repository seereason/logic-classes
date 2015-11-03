-- | Do satisfiability computations on any FirstOrderFormula formula
-- by converting it to a convenient instance of PropositionalFormula
-- and using the satisfiable function from that instance.  Currently
-- we use the satisfiable function from the PropLogic package, by the
-- Bucephalus project - it is much faster than a naive implementation
-- such as Prop.satisfiable.
{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
module Data.Logic.Satisfiable
    ( satisfiable
    , theorem
    , inconsistant
    , invalid
    ) where

import Data.List as List (map)
import Data.Logic.Instances.PropLogic ()
import Data.Set as Set (toList)
import FOL (HasApply(TermOf, PredOf), IsFirstOrder, IsQuantified(VarOf), IsTerm(FunOf))
import Formulas ((.~.), IsFormula(AtomOf))
import Lib (Marked)
import Lit (Literal)
import Prop (convertPropositional, Propositional, simpcnf)
import qualified PropLogic as PL -- ()
import Pretty (HasFixity, Pretty, )
import Skolem (HasSkolem(SVarOf), runSkolem, skolemize)

-- |Is there any variable assignment that makes the formula true?
-- satisfiable :: forall formula atom term v f m. (Monad m, IsQuantified formula atom v, Formula atom term v, IsTerm term v f, Ord formula, IsLiteral formula atom v, Ord atom) =>
--                 formula -> SkolemT v term m Bool
satisfiable :: forall formula atom v term function.
               (IsFirstOrder formula,
                HasSkolem function, Ord formula,
                atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
                v ~ VarOf formula, v ~ SVarOf function) =>
               formula -> Bool
satisfiable f =
    (PL.satisfiable . PL.CJ . List.map (PL.DJ . List.map convert) . List.map Set.toList . Set.toList . simpcnf id . skolemize') f
    where
      skolemize' = ((runSkolem . skolemize id) :: formula -> Marked Propositional formula)
      convert :: Marked Literal (Marked Propositional formula) -> PL.PropForm atom
      convert = convertPropositional id

-- |Is the formula always false?  (Not satisfiable.)
inconsistant :: forall formula atom v term p function.
                (atom ~ AtomOf formula, term ~ TermOf atom, p ~ PredOf atom, v ~ VarOf formula, v ~ SVarOf function, function ~ FunOf term,
                 IsFirstOrder formula,
                 HasSkolem function,
                 Eq formula, Ord formula, Pretty formula,
                 Ord atom, Pretty atom, HasFixity atom) =>
                formula -> Bool
inconsistant f =  not (satisfiable f)

-- |Is the negation of the formula inconsistant?
theorem :: forall formula atom v term p function.
           (atom ~ AtomOf formula, term ~ TermOf atom, p ~ PredOf atom, v ~ VarOf formula, v ~ SVarOf function, function ~ FunOf term,
            IsFirstOrder formula,
            HasSkolem function,
            Eq formula, Ord formula, Pretty formula,
            Ord atom, Pretty atom, HasFixity atom) =>
           formula -> Bool
theorem f = inconsistant ((.~.) f)

-- |A formula is invalid if it is neither a theorem nor inconsistent.
invalid :: forall formula atom v term p function.
           (atom ~ AtomOf formula, term ~ TermOf atom, p ~ PredOf atom, v ~ VarOf formula, v ~ SVarOf function, function ~ FunOf term,
            IsFirstOrder formula,
            HasSkolem function,
            Eq formula, Ord formula, Pretty formula,
            Ord atom, Pretty atom, HasFixity atom) =>
           formula -> Bool
invalid f = not (inconsistant f || theorem f)
