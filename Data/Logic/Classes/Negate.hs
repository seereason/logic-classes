module Data.Logic.Classes.Negate
     ( Negatable(..)
     , negated
     , (.~.)
     , (¬)
     , negative
     , positive
     ) where

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'Literal' class.
class Negatable formula where
    -- | Negate a formula in a naive fashion, the operators below
    -- prevent double negation.
    negatePrivate :: formula -> formula
    -- | Test whether a formula is negated or normal
    foldNegation :: (formula -> r) -- ^ called for normal formulas
                 -> (formula -> r) -- ^ called for negated formulas
                 -> formula -> r
-- | Is this formula negated at the top level?
negated :: Negatable formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

-- | Negate the formula, avoiding double negation
(.~.) :: Negatable formula => formula -> formula
(.~.) = foldNegation negatePrivate id

(¬) :: Negatable formula => formula -> formula
(¬) = (.~.)

infix 5 .~., ¬

-- ------------------------------------------------------------------------- 
-- Some operations on literals.  (These names are used in Harrison's code.)
-- ------------------------------------------------------------------------- 

negative :: Negatable formula => formula -> Bool
negative = negated

positive :: Negatable formula => formula -> Bool
positive = not . negative
