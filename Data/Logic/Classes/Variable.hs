module Data.Logic.Classes.Variable
    ( Variable(one, next)
    , variant
    ) where

import qualified Data.Set as S

-- |A class for finding unused variable names.  The next method
-- returns the next in an endless sequence of variable names, if we
-- keep calling it we are bound to find some unused name.
class Variable v where
    one :: v
    -- ^ Return some commonly used variable, typically x
    next :: v -> v
    -- ^ Return a different variable name, @iterate next one@ should
    -- return a list which never repeats.

-- |Find a variable name which is not in the variables set which is
-- stored in the monad.  This is initialized above with the free
-- variables in the formula.  (FIXME: this is not worth putting in
-- a monad, just pass in the set of free variables.)
variant :: (Variable v, Ord v) => S.Set v -> v -> v
variant names x = if S.member x names then variant names (next x) else x
