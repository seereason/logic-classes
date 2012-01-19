{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Data.Logic.Classes.Skolem where

import Data.Logic.Classes.Variable (Variable)

-- |This class shows how to convert between atomic Skolem functions
-- and Ints.  We include a variable type as a parameter because we
-- create skolem functions to replace an existentially quantified
-- variable, and it can be helpful to retain a reference to the
-- variable.
class Variable v => Skolem f v | f -> v where
    toSkolem :: v -> f
    -- ^ Built a Skolem function from the given variable and number.
    -- The number is generally obtained from the skolem monad.
    isSkolem  :: f -> Bool
