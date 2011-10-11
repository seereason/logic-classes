module Data.Logic.Classes.Boolean
    ( Boolean(fromBool)
    ) where

-- |Some types in the Logic class heirarchy need to have True and
-- False elements.
class Boolean p where
    fromBool :: Bool -> p
