module Data.Logic.Classes.Variable
    ( Variable(..)
    , variants
    , showVariable
    ) where

import qualified Data.Set as Set
import Text.PrettyPrint (Doc)

class Ord v => Variable v where
    variant :: v -> Set.Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.
    fromString :: String -> v
    -- ^ Build a variable based on a string.  This should also be
    -- removed, the Data.String.IsString class could be used instead.
    prettyVariable :: v -> Doc
    -- ^ Pretty print a variable

-- | Return an infinite list of variations on v
variants :: Variable v => v -> [v]
variants v0 =
    iter' Set.empty v0
    where iter' s v = let v' = variant v s in v' : iter' (Set.insert v s) v'

showVariable :: Variable v => v -> String
showVariable v = "fromString (" ++ show (show (prettyVariable v)) ++ ")"

{-
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
-}
