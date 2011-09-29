-- |Do satisfiability computations on any FirstOrderFormula formula by
-- converting it to a convenient instance of PropositionalFormula and
-- using the satisfiable function from that instance, in this case
-- the PropLogic package.
{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes #-}
module Data.Logic.Satisfiable
    ( clauses
    , satisfiable
    , theorem
    , inconsistant
    , invalid
    ) where

import qualified Data.Set as S
import Data.Logic.FirstOrder (FirstOrderFormula(..), toPropositional)
import Data.Logic.Logic ((.~.))
import Data.Logic.Monad (NormalT)
import Data.Logic.Normal (Literal)
import Data.Logic.NormalForm (clauseNormalForm)
import Data.Logic.Propositional.Instances.PropLogic ()
import qualified PropLogic as PL

satisfiable :: (Monad m, FirstOrderFormula formula term v p f, Ord formula, Literal formula term v p f) =>
                formula -> NormalT v term m Bool
satisfiable f = clauses f >>= return . PL.satisfiable

clauses :: forall m formula term v p f. (Monad m, FirstOrderFormula formula term v p f, Literal formula term v p f) =>
           formula -> NormalT v term m (PL.PropForm formula)
clauses f = clauseNormalForm f >>= return . PL.CJ . map (PL.DJ . map (toPropositional PL.A)) . map S.toList . S.toList

inconsistant :: (Monad m, FirstOrderFormula formula term v p f, Ord formula, Literal formula term v p f) =>
                formula -> NormalT v term m Bool
inconsistant f =  satisfiable f >>= return . not

theorem :: (Monad m, FirstOrderFormula formula term v p f, Ord formula, Literal formula term v p f) =>
           formula -> NormalT v term m Bool
theorem f = inconsistant ((.~.) f)

invalid :: (Monad m, FirstOrderFormula formula term v p f, Ord formula, Literal formula term v p f) =>
           formula -> NormalT v term m Bool
invalid f = inconsistant f >>= \ fi -> theorem f >>= \ ft -> return (not (fi || ft))
