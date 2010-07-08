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

import Data.String (IsString)
import Logic.FirstOrder (Skolem(..), FirstOrderLogic(..), toPropositional, HasSkolem(..))
import Logic.Logic ((.~.))
import Logic.NormalForm (clauseNormalForm)
import Logic.Instances.PropLogic ()
import PropLogic (PropForm(..), satisfiable)

clauses :: (FirstOrderLogic formula term v p f, Show formula, Eq formula, Eq term, HasSkolem m, Skolem f, IsString v) => formula -> m (PropForm formula)
clauses f = clauseNormalForm f >>= return . toPropositional A

inconsistant :: (FirstOrderLogic formula term v p f, Ord formula, Show formula, Eq term, HasSkolem m, Skolem f, IsString v) =>
                formula -> m Bool
inconsistant f = clauses f >>= return . not . satisfiable

theorem :: (FirstOrderLogic formula term v p f, Ord formula, Show formula, Eq term, HasSkolem m, Skolem f, IsString v) =>
           formula -> m Bool
theorem f = inconsistant ((.~.) f)

invalid :: (FirstOrderLogic formula term v p f, Ord formula, Show formula, Eq term, HasSkolem m, Skolem f, IsString v) =>
           formula -> m Bool
invalid f = theorem f >>= \ t -> inconsistant f >>= \ i -> return (not (t || i))
