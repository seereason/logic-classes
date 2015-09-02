{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Data.Logic.Classes.Skolem where

import Data.Logic.Classes.Variable (Variable)

-- | Skolem functions are created to replace an an existentially
-- quantified variable.  The idea is that if we have a predicate
-- P[x,y,z], and z is existentially quantified, then P is satisfiable
-- if there is at least one z that causes P to be true.  We postulate
-- a skolem function sKz[x,y] whose value is one of the z's that cause
-- P to be satisfied.  The value of sKz will depend on x and y, so we
-- make these parameters.  Thus we have eliminated existential
-- quantifiers and obtained the formula P[x,y,sKz[x,y]].
class Variable v => Skolem f v | f -> v where
    toSkolem :: v -> f     -- ^ Turn a variable into the corresponding skolem function
    fromSkolem  :: f -> Maybe v
    -- ^ If this is a skolem function return the variable it replaced.
    -- This used to be a predicate, but a Maybe v helps implement the
    -- Show instance.
