{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
-- | Substitution and finding variables are two basic operations on
-- formulas that contain terms and variables.  If a formula type
-- supports quantifiers we can also find free variables, otherwise all
-- variables are considered free.
module Data.Logic.Classes.Formula
    ( Formula(..)
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set

class Formula formula term v | formula -> term v where
    substitute :: Map.Map v term -> formula -> formula
    allVariables :: formula -> Set.Set v
    freeVariables :: formula -> Set.Set v
