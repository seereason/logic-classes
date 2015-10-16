-- |Do satisfiability computations on any FirstOrderFormula formula by
-- converting it to a convenient instance of PropositionalFormula and
-- using the satisfiable function from that instance.  Currently we
-- use the satisfiable function from the PropLogic package, by the
-- Bucephalus project.
{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Data.Logic.Satisfiable
    ( satisfiable
    , theorem
    , inconsistant
    , invalid
    ) where

import qualified Data.Set as Set
import Formulas ((.~.))
import Skolem (SkolemT)
import Data.Logic.Instances.PropLogic ()
import ATP (convertPropositional, HasFixity, IsFirstOrder, Pretty, simpcnf')
import qualified PropLogic as PL

-- |Is there any variable assignment that makes the formula true?
-- satisfiable :: forall formula atom term v f m. (Monad m, IsQuantified formula atom v, Formula atom term v, IsTerm term v f, Ord formula, IsLiteral formula atom v, Ord atom) =>
--                 formula -> SkolemT v term m Bool
satisfiable :: forall m formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Monad m, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
               formula -> SkolemT m Bool
satisfiable f =
    do let (clauses :: Set.Set (Set.Set formula)) = simpcnf' f
       let f' = PL.CJ . map (PL.DJ . map (convertPropositional id)) . map Set.toList . Set.toList $ clauses
       return . PL.satisfiable $ f'

-- |Is the formula always false?  (Not satisfiable.)
inconsistant :: forall m formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Monad m, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
                formula -> SkolemT m Bool
inconsistant f =  satisfiable f >>= return . not

-- |Is the negation of the formula inconsistant?
theorem :: forall m formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Monad m, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
           formula -> SkolemT m Bool
theorem f = inconsistant ((.~.) f)

-- |A formula is invalid if it is neither a theorem nor inconsistent.
invalid :: forall m formula atom v term p f. (IsFirstOrder formula atom p term v f, Ord atom, Monad m, Eq formula, Ord formula, Pretty atom, HasFixity atom) =>
           formula -> SkolemT m Bool
invalid f = inconsistant f >>= \ fi -> theorem f >>= \ ft -> return (not (fi || ft))
