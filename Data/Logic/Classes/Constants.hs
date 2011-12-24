module Data.Logic.Classes.Constants
    ( Constants(..)
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

(⊨) :: Constants formula => formula
(⊨) = true
(⊭) :: Constants formula => formula
(⊭) = false
