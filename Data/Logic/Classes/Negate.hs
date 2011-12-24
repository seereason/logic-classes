module Data.Logic.Classes.Negate
     ( Negatable(..)
     , (¬)
     ) where

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'Literal' class.
class Negatable formula where
    -- | Is this formula negated at the top level?
    negated :: formula -> Bool
    -- | Negate a formula
    (.~.) :: formula -> formula

(¬) :: Negatable formula => formula -> formula
(¬) = (.~.)

infix 5 .~., ¬
