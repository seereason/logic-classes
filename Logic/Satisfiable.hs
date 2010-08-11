-- |Do satisfiability computations on any FirstOrderLogic formula by
-- converting it to a convenient instance of PropositionalLogic and
-- using the satisfiable function from that instance, in this case
-- the PropLogic package.
{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Logic.Satisfiable
    ( clauses
    , satisfiable
    , theorem
    , inconsistant
    , invalid
    ) where

import Logic.FirstOrder (FirstOrderLogic(..), toPropositional)
import Logic.Logic ((.~.))
import Logic.NormalForm (clausalNormalForm)
import Logic.Instances.PropLogic ()
import qualified PropLogic as PL

satisfiable :: (FirstOrderLogic formula term v p f, Ord formula, Enum v) =>
                formula -> Bool
satisfiable =  PL.satisfiable . clauses

clauses :: (FirstOrderLogic formula term v p f, Ord formula, Enum v) => formula -> PL.PropForm formula
clauses f = PL.CJ (map (PL.DJ . map (toPropositional PL.A)) (clausalNormalForm f))

inconsistant :: (FirstOrderLogic formula term v p f, Ord formula, Enum v) =>
                formula -> Bool
inconsistant =  not . satisfiable

theorem :: (FirstOrderLogic formula term v p f, Ord formula, Enum v) =>
           formula -> Bool
theorem f = inconsistant ((.~.) f)

invalid :: (FirstOrderLogic formula term v p f, Ord formula, Enum v) =>
           formula -> Bool
invalid f = not (inconsistant f || theorem f)
