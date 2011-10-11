module Data.Logic.Classes.Negatable where

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'Literal' class.
class Negatable formula where
    -- | Is this negated at the top level?
    negated :: formula -> Bool
    -- | Negation (This needs to check for and remove double negation)
    (.~.) :: formula -> formula
