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
    ( Literal(..)
    , Implicative(..)
    ) where

import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic
--import Logic.Instances.Chiou ()

-- |A class to represent the literals and negated literals, also
-- called atomic functions, which appear in the Implicative and
-- Clausal Normal Forms.
class Boolean p => Literal lit term p | lit -> term, lit -> p, term -> p where
    litEqual :: Bool -> term -> term -> lit
    litPredicate :: Bool -> p -> [term] -> lit
    litFold :: (Bool -> term -> term -> r) ->
               (Bool -> p -> [term] -> r) ->
               lit ->
               r
-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e & f@,
-- where a thru f are literals.
class Literal lit term p => Implicative inf lit term p | inf -> lit , inf -> term, inf -> p where
    neg :: inf -> S.Set lit  -- ^ Return the literals that are negated and disjuncted on the left side of the implies
    pos :: inf -> S.Set lit  -- ^ Return the literals that are conjuncted on the right side of the implies
    fromINF :: forall formula term2 v p2 f. FirstOrderLogic formula term2 v p2 f =>
               (term -> term2) -> (p -> p2) -> inf -> formula
    fromINF ct cp inf =
        case (S.elems (neg inf), S.elems (pos inf)) of
          ([], []) -> (pApp (fromBool False) []) .=>. (pApp (fromBool True) [])
          ([], ors) -> disj ors
          (ands, []) -> (.~.) (conj ands)
          (ands, ors) -> (disj ors) .=>. (conj ands)
        where
          conj [] = error "True"
          conj [x] = lit x
          conj (x:xs) = (lit x) .&. (conj xs)
          disj :: [lit] -> formula
          disj [] = error "False"
          disj [x] = lit x
          disj (x:xs) = (lit x) .|. (disj xs)
          lit :: lit -> formula
          lit = litFold equal predicate
          equal :: Bool -> term -> term -> formula
          equal neg' t1 t2 = if neg' then (t1' .!=. t2') else (t1' .=. t2') where t1' = ct t1; t2' = ct t2
          predicate :: Bool -> p -> [term] -> formula
          predicate neg' p ts = if neg' then (.~.) x else x where x = pApp (cp p) (map ct ts)
