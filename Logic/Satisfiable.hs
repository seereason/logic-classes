-- |Do satisfiability computations on any PredicateLogic formula by
-- converting it to a convenient instance of PropositionalLogic and
-- using the satisfiable function from that instance, in this case
-- the PropLogic package.
{-# LANGUAGE FlexibleContexts #-}
module Logic.Satisfiable
    ( theorem
    , inconsistant
    , invalid
    ) where

import Logic.Logic ((.~.))
import Logic.NormalForm (clauseNormalForm)
import Logic.Predicate (PredicateLogic(..), Skolem(..), toPropositional)
import Logic.Instances.PropLogic ()
import PropLogic (PropForm(..), satisfiable)

theorem :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
           formula -> Bool
theorem = maybe (error "Failure in CNF") satisfiable . toPropositional (Just . A) . clauseNormalForm . (.~.)

inconsistant :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
                formula -> Bool
inconsistant f = theorem ((.~.) f)

invalid :: (PredicateLogic formula term v p f, Skolem v f, Ord formula, Show formula, Eq term) =>
           formula -> Bool
invalid f = not (theorem f || theorem ((.~.) f))
