-- |Do satisfiability computations on any PredicateLogic formula by
-- converting it to a convenient instance of PropositionalLogic and
-- using the satisfiable function from that instance, in this case
-- the PropLogic package.
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Logic.Satisfiable
    ( clauses
    , theorem
    , inconsistant
    , invalid
    ) where

import Logic.Logic ((.~.))
import Logic.NormalForm (clauseNormalForm)
import Logic.Predicate (Skolem(..), PredicateLogic(..), toPropositional)
--import Logic.Instances.Parameterized (Formula(..))
import Logic.Instances.PropLogic ()
import PropLogic (PropForm(..), satisfiable)

clauses :: (PredicateLogic formula term v p f, Show formula, Eq formula, Eq term, Skolem m f) => formula -> m (PropForm formula)
clauses f = clauseNormalForm f >>= return . toPropositional A

inconsistant :: (PredicateLogic formula term v p f, Ord formula, Show formula, Eq term, Skolem m f) =>
                formula -> m Bool
inconsistant f = clauses f >>= return . not . satisfiable

theorem :: (PredicateLogic formula term v p f, Ord formula, Show formula, Eq term, Skolem m f) =>
           formula -> m Bool
theorem f = inconsistant ((.~.) f)

invalid :: (PredicateLogic formula term v p f, Ord formula, Show formula, Eq term, Skolem m f) =>
           formula -> m Bool
invalid f = theorem f >>= \ t -> inconsistant f >>= \ i -> return (not (t || i))
