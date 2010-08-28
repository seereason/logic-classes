{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}

module Logic.Implicative
    ( Implicative(..)
    , toImplicative
    , fromImplicative
    ) where

import qualified Data.Set as S
import Logic.Clause (Literal(..))
import Logic.FirstOrder
import Logic.Logic

-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e |
-- f@, where a thru f are literals.  One more restriction that is not
-- implied by the type is that no literal can appear in both the pos
-- set and the neg set.  Minimum implementation: pos, neg, toINF
class (Literal lit, Eq inf) => Implicative inf lit | inf -> lit where
    neg :: inf -> S.Set lit
                         -- ^ Return the literals that are negated
                         -- and disjuncted on the left side of the
                         -- implies.  @neg@ and @pos@ are sets in
                         -- some sense, but we don't (yet) have
                         -- suitable Eq and Ord instances that
                         -- understand renaming.
    pos :: inf -> S.Set lit
                         -- ^ Return the literals that are
                         -- conjuncted on the right side of the
                         -- implies.
    makeINF :: S.Set lit -> S.Set lit -> inf

toImplicative :: (FirstOrderLogic formula term v p f, Implicative inf lit, Eq formula, Eq lit) =>
                 (formula -> lit) -> [([formula], [formula])] -> [inf]
toImplicative toLit = map (\ (n, p) -> makeINF (S.fromList (map toLit n)) (S.fromList (map toLit p)))

fromImplicative :: (FirstOrderLogic formula term v p f, Implicative inf lit) =>
                   (lit -> formula) -> inf -> formula -- ^ Convert implicative to first order
fromImplicative fromLit inf =
    (disj (map fromLit (S.toList (neg inf)))) .=>. (conj (map fromLit (S.toList (pos inf))))
