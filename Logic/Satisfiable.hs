-- |Do satisfiability computations on any FirstOrderLogic formula by
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

import Logic.FirstOrder (FirstOrderLogic(..), toPropositional)
import Logic.Logic ((.~.))
import Logic.NormalForm (clauseNormalForm)
import Logic.Instances.PropLogic ()
import PropLogic (PropForm(..), satisfiable)

clauses :: (FirstOrderLogic formula term v p f, Ord formula, Show formula) => formula -> PropForm formula
clauses = toPropositional A . clauseNormalForm

inconsistant :: (FirstOrderLogic formula term v p f, Ord formula, Show formula) =>
                formula -> Bool
inconsistant =  not . satisfiable . clauses

theorem :: (FirstOrderLogic formula term v p f, Ord formula, Show formula) =>
           formula -> Bool
theorem f = inconsistant ((.~.) f)

invalid :: (FirstOrderLogic formula term v p f, Ord formula, Show formula) =>
           formula -> Bool
invalid f = not (inconsistant f || theorem f)
