{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}

module Logic.Implicative
    ( Implicative(..)
    ) where

import Logic.FirstOrder
import Logic.Logic

-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e |
-- f@, where a thru f are literals.  One more restriction that is not
-- implied by the type is that no literal can appear in both the pos
-- set and the neg set.  Minimum implementation: pos, neg, toINF
class FirstOrderLogic formula term v p f => Implicative inf formula term v p f | inf -> formula, inf -> term where
    neg :: inf -> [formula]  -- ^ Return the literals that are negated
                             -- and disjuncted on the left side of the
                             -- implies.  @neg@ and @pos@ are sets in
                             -- some sense, but we don't (yet) have
                             -- suitable Eq and Ord instances that
                             -- understand renaming.
    pos :: inf -> [formula]  -- ^ Return the literals that are
                             -- conjuncted on the right side of the
                             -- implies.
    toImplicative :: formula -> [inf] -- ^ Convert a first order logic formula to implicative normal form
    fromImplicative :: inf -> formula -- ^ Convert implicative to first order
    fromImplicative inf =
        (disj (neg inf)) .=>. (conj (pos inf))
        where
          conj :: [formula] -> formula
          conj [] = pApp (fromBool True) []
          conj [x] = x
          conj (x:xs) = (x) .&. (conj xs)
          disj :: [formula] -> formula
          disj [] = pApp (fromBool False) []
          disj [x] = x
          disj (x:xs) = (x) .|. (disj xs)
