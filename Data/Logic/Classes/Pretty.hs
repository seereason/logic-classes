-- | The intent of this class is to be similar to Show, but only one
-- way, with no corresponding Read class.  It doesn't really belong
-- here in logic-classes.  To put something in a pretty printing class
-- implies that there is only one way to pretty print it, which is not
-- an assumption made by Text.PrettyPrint.  But in practice this is
-- often good enough.
module Data.Logic.Classes.Pretty
    ( Pretty(pretty)
    ) where

import Text.PrettyPrint (Doc)

class Pretty x where
    pretty :: x -> Doc
