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
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), toPropositional)
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term)
import Data.Logic.Harrison.Skolem (SkolemT)
import Data.Logic.Instances.PropLogic ()
import Data.Logic.Normal.Clause (clauseNormalForm)
import qualified PropLogic as PL

-- |Is there any variable assignment that makes the formula true?
-- satisfiable :: forall formula atom term v f m. (Monad m, FirstOrderFormula formula atom v, Formula atom term v, Term term v f, Ord formula, Literal formula atom v, Ord atom) =>
--                 formula -> SkolemT v term m Bool
satisfiable :: forall m formula atom v term f. (FirstOrderFormula formula atom v, Literal formula atom v, Term term v f, Formula atom term v,
                                                Ord atom, Monad m, Eq formula, Ord formula) =>
               formula -> SkolemT v term m Bool
satisfiable f =
    do (clauses :: Set.Set (Set.Set formula)) <- clauseNormalForm f
       let f' = PL.CJ . map (PL.DJ . map (toPropositional PL.A)) . map Set.toList . Set.toList $ clauses
       return . PL.satisfiable $ f'

-- |Is the formula always false?  (Not satisfiable.)
inconsistant :: forall m formula atom v term f. (FirstOrderFormula formula atom v, Literal formula atom v, Term term v f, Formula atom term v,
                                                 Ord atom, Monad m, Eq formula, Ord formula) =>
                formula -> SkolemT v term m Bool
inconsistant f =  satisfiable f >>= return . not

-- |Is the negation of the formula inconsistant?
theorem :: forall m formula atom v term f. (FirstOrderFormula formula atom v, Literal formula atom v, Term term v f, Formula atom term v,
                                            Ord atom, Monad m, Eq formula, Ord formula) =>
           formula -> SkolemT v term m Bool
theorem f = inconsistant ((.~.) f)

-- |A formula is invalid if it is neither a theorem nor inconsistent.
invalid :: forall m formula atom v term f. (FirstOrderFormula formula atom v, Literal formula atom v, Term term v f, Formula atom term v,
                                            Ord atom, Monad m, Eq formula, Ord formula) =>
           formula -> SkolemT v term m Bool
invalid f = inconsistant f >>= \ fi -> theorem f >>= \ ft -> return (not (fi || ft))
