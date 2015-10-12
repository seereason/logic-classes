{-# LANGUAGE FlexibleInstances #-}
module Data.Logic.Classes.Constants
    ( HasBoolean(asBool, fromBool)
    , ifElse
    , true
    , (⊨)
    , false
    , (⊭)
    , prettyBool
    ) where

import Data.Logic.Classes.Pretty (Pretty(pPrint), Logic(..))
import Text.PrettyPrint (Doc, text)

-- |Some types in the Logic class heirarchy need to have True and
-- False elements.
class HasBoolean p where
    asBool :: p -> Maybe Bool
    fromBool :: Bool -> p

true :: HasBoolean p => p
true = fromBool True

false :: HasBoolean p => p
false = fromBool False

ifElse :: a -> a -> Bool -> a
ifElse t _ True = t
ifElse _ f False = f

(⊨) :: HasBoolean formula => formula
(⊨) = true
(⊭) :: HasBoolean formula => formula
(⊭) = false

prettyBool :: Bool -> Doc
prettyBool True = text "⊨"
prettyBool False = text "⊭"

instance Pretty (Logic Bool) where
    pPrint = prettyBool . unLogic
