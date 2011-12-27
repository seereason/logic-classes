module Data.Logic.Classes.Constants
    ( Constants(..)
    , asBool
    , (⊨)
    , (⊭)
    ) where

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

(⊨) :: Constants formula => formula
(⊨) = true
(⊭) :: Constants formula => formula
(⊭) = false
