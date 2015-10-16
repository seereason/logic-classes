{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Data.Logic.Classes.ClauseNormalForm
    ( ClauseNormalFormula(clauses, makeCNF, satisfiable)
    ) where

import Control.Monad (MonadPlus)
import Data.Set as S
import Formulas

-- |A class to represent formulas in CNF, which is the conjunction of
-- a set of disjuncted literals each which may or may not be negated.
class (IsNegatable lit, Eq lit, Ord lit) => ClauseNormalFormula cnf lit | cnf -> lit where
    clauses :: cnf -> S.Set (S.Set lit)
    makeCNF :: S.Set (S.Set lit) -> cnf
    satisfiable :: MonadPlus m => cnf -> m Bool
