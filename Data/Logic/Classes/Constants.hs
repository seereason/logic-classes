module Data.Logic.Classes.Constants
    ( Constants(..)
    , asBool
    , ifElse
    , (⊨)
    , (⊭)
    , prettyBool
    ) where

import Text.PrettyPrint (Doc, text)

-- |Some types in the Logic class heirarchy need to have True and
-- False elements.
class Constants p where
    fromBool :: Bool -> p
    true :: p
    true = fromBool True
    false :: p
    false = fromBool False

asBool :: (Eq p, Constants p) => p -> Maybe Bool 
asBool p | p == true = Just True
         | p == false = Just False
         | True = Nothing

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