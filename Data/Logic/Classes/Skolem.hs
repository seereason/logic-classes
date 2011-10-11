module Data.Logic.Classes.Skolem where

-- |This class shows how to convert between atomic Skolem functions
-- and Ints.
class Skolem f where
    toSkolem :: Int -> f
    fromSkolem  :: f -> Maybe Int
