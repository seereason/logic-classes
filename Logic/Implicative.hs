{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}

module Logic.Implicative
    ( Implicative(..)
    , toImplicative
    , fromImplicative
    ) where

import Logic.Clause (Literal(..))
import Logic.FirstOrder
import Logic.Logic

-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e |
-- f@, where a thru f are literals.  One more restriction that is not
-- implied by the type is that no literal can appear in both the pos
-- set and the neg set.  Minimum implementation: pos, neg, toINF
class Literal lit => Implicative inf lit | inf -> lit where
    neg :: inf -> [lit]  -- ^ Return the literals that are negated
                         -- and disjuncted on the left side of the
                         -- implies.  @neg@ and @pos@ are sets in
                         -- some sense, but we don't (yet) have
                         -- suitable Eq and Ord instances that
                         -- understand renaming.
    pos :: inf -> [lit]  -- ^ Return the literals that are
                         -- conjuncted on the right side of the
                         -- implies.
    makeINF :: [lit] -> [lit] -> inf

toImplicative :: (FirstOrderLogic formula term v p f, Implicative inf clause, Eq formula, Eq clause) =>
                 (formula -> clause) -> [([formula], [formula])] -> [inf]
toImplicative clause = map (\ (n, p) -> makeINF (map clause n) (map clause p))

fromImplicative :: (FirstOrderLogic formula term v p f, Implicative inf lit) =>
                   (lit -> formula) -> inf -> formula -- ^ Convert implicative to first order
fromImplicative clause inf =
    (disj (map clause (neg inf))) .=>. (conj (map clause (pos inf)))
