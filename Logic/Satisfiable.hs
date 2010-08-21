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

import qualified Data.Set as S
import Logic.Clause (Literal)
import Logic.FirstOrder (FirstOrderLogic(..), toPropositional)
import Logic.Logic ((.~.))
import Logic.Monad (NormalT)
import Logic.NormalForm (clauseNormalForm)
import Logic.Instances.PropLogic ()
import qualified PropLogic as PL

satisfiable :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Ord formula) =>
                formula -> NormalT v term m Bool
satisfiable f = clauses f >>= return . PL.satisfiable

clauses :: (Monad m, FirstOrderLogic formula term v p f, Literal formula) => formula -> NormalT v term m (PL.PropForm formula)
clauses f = clauseNormalForm f >>= return . PL.CJ . map (PL.DJ . map (toPropositional PL.A)) . map S.toList . S.toList

inconsistant :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Ord formula) =>
                formula -> NormalT v term m Bool
inconsistant f =  satisfiable f >>= return . not

theorem :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Ord formula) =>
           formula -> NormalT v term m Bool
theorem f = inconsistant ((.~.) f)

invalid :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Ord formula) =>
           formula -> NormalT v term m Bool
invalid f = inconsistant f >>= \ fi -> theorem f >>= \ ft -> return (not (fi || ft))
