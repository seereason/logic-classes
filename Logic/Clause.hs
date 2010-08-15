{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wwarn #-}
-- |Once a formula is converted to CNF, this module can be used to
-- convert it to any type which is an instance of Clausal, e.g. the
-- CNF types defined in the parse-dimacs and funsat packages.
module Logic.Clause
    ( ClauseNormal(..)
    , Literal(..)
    , toClauseNormal
    , toClauseNormalM
    , fromClauseNormal
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.Writer (MonadPlus)
import Logic.FirstOrder
import Logic.Logic
import Prelude hiding (negate)

-- |A class to represent formulas in CNF, which is the conjunction of
-- a set of disjuncted literals each which may or may not be negated.
class Literal lit => ClauseNormal cnf lit | cnf -> lit where
    clauses :: cnf -> [[lit]]
    makeCNF :: [[lit]] -> cnf
    satisfiable :: MonadPlus m => cnf -> m Bool

-- |The literals in a ClauseNormal formula.
class (Eq lit, Ord lit) => Literal lit where
    negate :: lit -> lit
    negated :: lit -> Bool

-- |Convert a FirstOrderLogic formula which has been put into clausal
-- form to another (typically simpler) type which is just an instance
-- of ClauseNormal.
toClauseNormal :: forall formula term v p f cnf lit. (FirstOrderLogic formula term v p f, Eq formula, ClauseNormal cnf lit) =>
             (formula -> lit) -> [[formula]] -> cnf
toClauseNormal lit formula = runIdentity . toClauseNormalM (return . lit) $ formula

-- |A version of toClauseNormal which uses a monad to create the literals.
-- This is necessary if the literals in the ClauseNormal instance are less
-- expressive than those in the formula, e.g. in the CNF type in
-- parse-dimacs the literals are just Ints, while in our formula they
-- are usually string-like.  In this case we need to use a state monad
-- to build a mapping from formula literals to CNF literals.
toClauseNormalM :: forall formula term v p f cnf lit m. (Monad m, FirstOrderLogic formula term v p f, Eq formula, ClauseNormal cnf lit, Eq lit, Pretty v, Pretty p, Pretty f) =>
             (formula -> m lit) -> [[formula]] -> m cnf
toClauseNormalM lit formula =
    -- If any of the elements of a disjunction is the whole
    -- disjunction is true, so it has no effect on the conjunction.
    mapM (mapM lit) formula >>= return . makeCNF

-- |Convert an instance of ClauseNormal into an instance of FirstOrderLogic.
fromClauseNormal :: forall formula term v p f cnf lit. (FirstOrderLogic formula term v p f, ClauseNormal cnf lit, Show lit) =>
                   (lit -> formula) -> cnf -> formula
fromClauseNormal lit cform =
    conj (map (disj . map lit') (clauses cform))
    where
      lit' x | negated x =  (.~.) (lit (negate x))
      lit' x = lit x
