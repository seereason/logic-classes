module Data.Logic.Classes.Constants
    ( Constants(asBool, fromBool)
    , ifElse
    , true
    , (⊨)
    , false
    , (⊭)
    , prettyBool
    ) where

import Data.Logic.Classes.Pretty (Pretty(pretty))
import Text.PrettyPrint (Doc, text)

-- |Some types in the Logic class heirarchy need to have True and
-- False elements.
class Constants p where
    asBool :: p -> Maybe Bool
    fromBool :: Bool -> p

true :: Constants p => p
true = fromBool True

false :: Constants p => p
false = fromBool False

ifElse :: a -> a -> Bool -> a
ifElse t _ True = t
ifElse _ f False = f

(⊨) :: Constants formula => formula
(⊨) = true
(⊭) :: Constants formula => formula
(⊭) = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊨"
prettyBool False = text "⊭"

instance Pretty Bool where
    pretty = prettyBool
