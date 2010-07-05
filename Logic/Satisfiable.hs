-- |Do satisfiability computations on any PredicateLogic formula by
-- converting it to a convenient instance of PropositionalLogic and
-- using the satisfiable function from that instance, in this case
-- the PropLogic package.
{-# LANGUAGE FlexibleContexts #-}
module Logic.Satisfiable
    ( clauses
    , theorem
    , inconsistant
    , invalid
    ) where

import Logic.Logic ((.~.))
import Logic.NormalForm (clauseNormalForm)
import Logic.Predicate (PredicateLogic(..), Skolem(..), toPropositional)
--import Logic.Instances.Parameterized (Formula(..))
import Logic.Instances.PropLogic ()
import PropLogic (PropForm(..), satisfiable)

clauses :: (PredicateLogic formula term v p f, Show formula, Skolem v f, Eq formula, Eq term) => formula -> PropForm formula
clauses = maybe (error "Failure in Logic.NormalForm.cnf") id . toPropositional (Just . A) . clauseNormalForm

inconsistant :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
                formula -> Bool
inconsistant = not . satisfiable . clauses

theorem :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
           formula -> Bool
theorem = inconsistant . (.~.)

invalid :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
           formula -> Bool
invalid f = not (theorem f || inconsistant f)
