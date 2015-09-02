module Data.Logic.Classes.Variable
    ( Variable(..)
    , variants
    , showVariable
    ) where

import Data.Data (Data)
import Data.Logic.Classes.Pretty (Pretty)
import qualified Data.Set as Set
import Data.String (IsString)
import Text.PrettyPrint (Doc)

class (Ord v, IsString v, Data v, Pretty v) => Variable v where
    variant :: v -> Set.Set v -> v
    -- ^ Return a variable based on v but different from any set
    -- element.  The result may be v itself if v is not a member of
    -- the set.
    prefix :: String -> v -> v
    -- ^ Modify a variable by adding a prefix.  This unfortunately
    -- assumes that v is "string-like" but at least one algorithm in
    -- Harrison currently requires this.
    prettyVariable :: v -> Doc
    -- ^ Pretty print a variable

-- | Return an infinite list of variations on v
variants :: Variable v => v -> [v]
variants v0 =
    iter' Set.empty v0
    where iter' s v = let v' = variant v s in v' : iter' (Set.insert v s) v'

showVariable :: Variable v => v -> String
showVariable v = "(fromString (" ++ show (show (prettyVariable v)) ++ "))"
