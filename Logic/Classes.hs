{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Logic.Classes
    ( FormulaC(..)
    , AtomicPredicateC
    ) where

import Data.Data (Data)
import Data.Typeable (Typeable)

-- |The functional dependencies are necessary here so we can write functions
-- that don't involve all three of the type parameters.  For example, without 
-- them the univquant_free_vars function gives the error 
-- 
--    No instance for (C.Formula Formula t V)
-- 
-- I guess because the function doesn't fix the Term type.
class FormulaC f t v | f -> t, f -> v where
    for_all :: [v] -> f -> f  -- ^ Universal quantification
    exists :: [v] -> f -> f   -- ^ Existential quantification
    (.<=>.) :: f -> f -> f    -- ^ Equivalence
    (.=>.) :: f -> f -> f     -- ^ Implication
    (.<=.) :: f -> f -> f     -- ^ Reverse implication
    (.|.) :: f -> f -> f      -- ^ Disjunction/OR
    (.&.) :: f -> f -> f      -- ^ Conjunction/AND
    (.<~>.) :: f -> f -> f    -- ^ XOR
    (.~|.) :: f -> f -> f     -- ^ NOR
    (.~&.) :: f -> f -> f     -- ^ NAND
    (.~.) :: f -> f           -- ^ Negation
    (.=.) :: t -> t -> f      -- ^ Equality of Terms
    (.!=.) :: t -> t -> f     -- ^ Inequality of Terms

-- The main point of these functions is so we can assign these precedences.
                     
infixl 2  .<=>. ,  .=>. ,  .<=. ,  .<~>.
infixl 3  .|. ,  .~|.
infixl 4  .&. ,  .~&.
infixl 5  .=. ,  .!=.

class (Eq u, Ord u, Show u, Read u, Data u, Typeable u) => AtomicPredicateC u pred w | u -> pred, u -> w
