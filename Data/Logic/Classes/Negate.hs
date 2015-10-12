module Data.Logic.Classes.Negate
     ( IsNegatable(..)
     , negated
     , (.~.)
     , (¬)
     , negative
     , positive
     ) where

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the 'Literal' class.
class IsNegatable formula where
    -- | Negate a formula in a naive fashion, the operators below
    -- prevent double negation.
    naiveNegate :: formula -> formula
    -- | Test whether a formula is negated or normal
    foldNegation :: (formula -> r) -- ^ called for normal formulas
                 -> (formula -> r) -- ^ called for negated formulas
                 -> formula -> r
-- | Is this formula negated at the top level?
negated :: IsNegatable formula => formula -> Bool
negated = foldNegation (const False) (not . negated)

-- | Negate the formula, avoiding double negation
(.~.) :: IsNegatable formula => formula -> formula
(.~.) = foldNegation naiveNegate id

(¬) :: IsNegatable formula => formula -> formula
(¬) = (.~.)

infix 5 .~., ¬

-- ------------------------------------------------------------------------- 
-- Some operations on literals.  (These names are used in Harrison's code.)
-- ------------------------------------------------------------------------- 

negative :: IsNegatable formula => formula -> Bool
negative = negated

positive :: IsNegatable formula => formula -> Bool
positive = not . negative
