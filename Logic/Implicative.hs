{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
-- |A series of transformations to convert first order logic formulas
-- into (ultimately) Clause Normal Form.
-- 
-- @
-- 1st order formula:
--   ∀Y (∀X (taller(Y,X) | wise(X)) => wise(Y))
-- 
-- Simplify
--   ∀Y (~∀X (taller(Y,X) | wise(X)) | wise(Y))
-- 
-- Move negations in - Negation Normal Form
--   ∀Y (∃X (~taller(Y,X) & ~wise(X)) | wise(Y))
-- 
-- Move quantifiers out - Prenex Normal Form
--   ∀Y (∃X ((~taller(Y,X) & ~wise(X)) | wise(Y)))
-- 
-- Distribute disjunctions
--   ∀Y ∃X ((~taller(Y,X) | wise(Y)) & (~wise(X) | wise(Y)))
-- 
-- Skolemize  - Skolem Normal Form
--   ∀Y (~taller(Y,x(Y)) | wise(Y)) & (~wise(x(Y)) | wise(Y))
-- 
-- Convert to CNF
--   { ~taller(Y,x(Y)) | wise(Y),
--     ~wise(x(Y)) | wise(Y) } 
-- @
-- 
module Logic.Implicative
    ( Implicative(..)
    ) where

import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic

-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e &
-- f@, where a thru f are literals.  One more restriction that is not
-- implied by the type is that no literal can appear in both the pos
-- set and the neg set.  Minimum implementation: pos, neg, toINF
class FirstOrderLogic formula term v p f => Implicative inf formula term v p f | inf -> formula, inf -> term where
    neg :: inf -> S.Set formula  -- ^ Return the literals that are negated and disjuncted on the left side of the implies
    pos :: inf -> S.Set formula  -- ^ Return the literals that are conjuncted on the right side of the implies
    toImplicative :: formula -> [inf]
    fromImplicative :: inf -> formula
    fromImplicative inf =
        case (S.elems (neg inf), S.elems (pos inf)) of
          ([], []) -> (pApp (fromBool False) []) .=>. (pApp (fromBool True) [])
          ([], ors) -> disj ors
          (ands, []) -> (.~.) (conj ands)
          (ands, ors) -> (disj ors) .=>. (conj ands)
        where
          conj :: [formula] -> formula
          conj [] = error "True"
          conj [x] = x
          conj (x:xs) = (x) .&. (conj xs)
          disj :: [formula] -> formula
          disj [] = error "False"
          disj [x] = x
          disj (x:xs) = (x) .|. (disj xs)
