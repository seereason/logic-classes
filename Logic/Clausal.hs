{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wwarn #-}
-- |Once a formula is converted to CNF, this module can be used to
-- convert it to any type which is an instance of Clausal, e.g. the
-- CNF types defined in the parse-dimacs and funsat packages.
module Logic.Clausal
    ( Clausal(..)
    , Literal(..)
    , toClausal
    , toClausalM
    , fromClausal
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.Writer (MonadPlus)
import Logic.FirstOrder
import Logic.Logic
import Prelude hiding (negate)

-- |A class to represent formulas in CNF, which is the conjunction of
-- a set of disjuncted literals each which may or may not be negated.
class Literal lit => Clausal cnf lit | cnf -> lit where
    clauses :: cnf -> [[lit]]
    makeCNF :: [[lit]] -> cnf
    satisfiable :: MonadPlus m => cnf -> m Bool

-- |The literals in a Clausal formula.
class Literal lit where
    negate :: lit -> lit
    negated :: lit -> Bool

-- |Convert a FirstOrderLogic formula which has been put into clausal
-- form to another (typically simpler) type which is just an instance
-- of Clausal.
toClausal :: forall formula term v p f cnf lit. (FirstOrderLogic formula term v p f, Eq formula, Clausal cnf lit, Eq lit, Pretty v, Pretty p, Pretty f) =>
             (formula -> lit) -> [[formula]] -> cnf
toClausal lit formula = runIdentity . toClausalM (return . lit) $ formula

-- |A version of toClausal which uses a monad to create the literals.
-- This is necessary if the literals in the Clausal instance are less
-- expressive than those in the formula, e.g. in the CNF type in
-- parse-dimacs the literals are just Ints, while in our formula they
-- are usually string-like.  In this case we need to use a state monad
-- to build a mapping from formula literals to CNF literals.
toClausalM :: forall formula term v p f cnf lit m. (Monad m, FirstOrderLogic formula term v p f, Eq formula, Clausal cnf lit, Eq lit, Pretty v, Pretty p, Pretty f) =>
             (formula -> m lit) -> [[formula]] -> m cnf
toClausalM lit formula =
    -- If any of the elements of a disjunction is the whole
    -- disjunction is true, so it has no effect on the conjunction.
    mapM (mapM lit) formula >>= return . makeCNF

-- |Convert an instance of Clausal into an instance of FirstOrderLogic.
fromClausal :: forall formula term v p f cnf lit. (FirstOrderLogic formula term v p f, Clausal cnf lit, Show lit) =>
                   (lit -> formula) -> cnf -> formula
fromClausal lit cform =
    conj (map disj (clauses cform))
    where
      disj [] = pApp (fromBool False) []
      disj [x] = lit' x
      disj (x:xs) = lit' x .|. disj xs
      conj [] = pApp (fromBool True) []
      conj [x] = x
      conj (x:xs) = x .&. conj xs
      lit' x | negated x =  (.~.) (lit (negate x))
      lit' x = lit x
