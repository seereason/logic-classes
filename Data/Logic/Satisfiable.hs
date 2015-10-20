-- | Do satisfiability computations on any FirstOrderFormula formula
-- by converting it to a convenient instance of PropositionalFormula
-- and using the satisfiable function from that instance.  Currently
-- we use the satisfiable function from the PropLogic package, by the
-- Bucephalus project - it is much faster than a naive implementation
-- such as Prop.satisfiable.
{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Data.Logic.Satisfiable
    ( satisfiable
    , theorem
    , inconsistant
    , invalid
    ) where

import Data.Logic.Instances.PropLogic ()
import qualified Data.Set as Set
import FOL (IsFirstOrder)
import Formulas ((.~.))
import Prop (convertPropositional)
import qualified PropLogic as PL
import Pretty (HasFixity, Pretty, )
import Skolem (simpcnf')

-- |Is there any variable assignment that makes the formula true?
-- satisfiable :: forall formula atom term v f m. (Monad m, IsQuantified formula atom v, Formula atom term v, IsTerm term v f, Ord formula, IsLiteral formula atom v, Ord atom) =>
--                 formula -> SkolemT v term m Bool
satisfiable :: forall formula atom v term p f.
               (IsFirstOrder formula atom p term v f, Ord atom, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
               formula -> Bool
satisfiable f =
    (PL.satisfiable . PL.CJ . map (PL.DJ . map (convertPropositional id)) . map Set.toList . Set.toList . simpcnf') f

-- |Is the formula always false?  (Not satisfiable.)
inconsistant :: forall formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
                formula -> Bool
inconsistant f =  not (satisfiable f)

-- |Is the negation of the formula inconsistant?
theorem :: forall formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
           formula -> Bool
theorem f = inconsistant ((.~.) f)

-- |A formula is invalid if it is neither a theorem nor inconsistent.
invalid :: forall formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
           formula -> Bool
invalid f = not (inconsistant f || theorem f)
