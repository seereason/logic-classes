{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
-- | Substitution and finding variables are two basic operations on
-- formulas that contain terms and variables.  If a formula type
-- supports quantifiers we can also find free variables, otherwise all
-- variables are considered free.
module Data.Logic.Classes.Formula
    ( Formula(..)
    ) where

import Control.Applicative.Error (Failing)
import qualified Data.Map as Map
import qualified Data.Set as Set

class Formula formula term v | formula -> term v where
    substitute :: Map.Map v term -> formula -> formula
    allVariables :: formula -> Set.Set v
    freeVariables :: formula -> Set.Set v
    unify :: Map.Map v term -> formula -> formula -> Failing (Map.Map v term)
    -- unify2 :: atom -> atom -> Maybe (Map.Map v term, Map.Map v term)
    match :: Map.Map v term -> formula -> formula -> Failing (Map.Map v term) -- ^ Very similar to unify, not quite sure if there is a difference
    foldTerms :: (term -> r -> r) -> r -> formula -> r
    isRename :: formula -> formula -> Bool
    getSubst :: Map.Map v term -> formula -> Map.Map v term
    -- demodulate :: Unification atom v term -> Unification atom v term -> Maybe (Unification atom v term)

