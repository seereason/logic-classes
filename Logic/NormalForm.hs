{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
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
module Logic.NormalForm
    ( simplify
    , negationNormalForm
    , prenexNormalForm
    , skolemNormalForm
    , clauseNormalForm
    , trivial
    , cnfTrace
    , implicativeNormalForm
    ) where

import Control.Monad.State (MonadPlus, msum)
import Data.Generics (Data, Typeable, listify)
import Data.List (intersperse)
import Data.Maybe (isJust)
import Logic.FirstOrder
import Logic.Harrison.Skolem (prenex, askolemize, simplify, specialize)
import Logic.Harrison.Prop (nnf, trivial, simpcnf)
import Logic.Monad (NormalT)
import Logic.Normal (Literal(..), ImplicativeNormalForm, makeINF)
import qualified Logic.Set as S
import Text.PrettyPrint (hcat, vcat, text, nest, ($$), brackets, render)

-- | Simplify and recursively apply nnf.
negationNormalForm :: FirstOrderFormula formula term v p f => formula -> formula
negationNormalForm = nnf . simplify

-- |Convert to Prenex normal form, with all quantifiers at the left.
prenexNormalForm :: (FirstOrderFormula formula term v p f) => formula -> formula
prenexNormalForm = prenex . negationNormalForm

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (Monad m, FirstOrderFormula formula term v p f) => formula -> NormalT v term m formula
skolemNormalForm f = askolemize f >>= return . specialize . prenexNormalForm

-- |Convert to Skolem Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
clauseNormalForm :: (Monad m, FirstOrderFormula formula term v p f, Literal lit term v p f) =>
       formula -> NormalT v term m (S.Set (S.Set lit))
clauseNormalForm fm = skolemNormalForm fm >>= return . simpcnf id id id

cnfTrace :: forall m formula term v p f. (Monad m, FirstOrderFormula formula term v p f, Pretty v, Pretty p, Pretty f) =>
            formula -> NormalT v term m String
cnfTrace f =
    do let simplified = simplify f
           pnf = prenexNormalForm f
       snf <- skolemNormalForm f
       (cnf :: S.Set (S.Set formula)) <- clauseNormalForm f
       return . render . vcat $
                  [text "Original:" $$ nest 2 (prettyForm 0 f),
                   text "Simplified:" $$ nest 2 (prettyForm 0 simplified),
                   text "Negation Normal Form:" $$ nest 2 (prettyForm 0 (negationNormalForm f)),
                   text "Prenex Normal Form:" $$ nest 2 (prettyForm 0 pnf),
                   text "Skolem Normal Form:" $$ nest 2 (prettyForm 0 snf),
                   text "Clause Normal Form:" $$ vcat (map prettyClause (fromSS cnf))]
    where
      prettyClause = nest 2 . brackets . hcat . intersperse (text ", ") . map (nest 2 . brackets . prettyForm 0)
      fromSS = (map S.toList) . S.toList 

-- |Take the clause normal form, and turn it into implicative form,
-- where each clauses becomes an (LHS, RHS) pair with the negated
-- literals on the LHS and the non-negated literals on the RHS:
-- @
--   (a | ~b | c | ~d) becomes (b & d) => (a | c)
--   (~b | ~d) | (a | c)
--   ~~(~b | ~d) | (a | c)
--   ~(b & d) | (a | c)
-- @
-- If there are skolem functions on the RHS, split the formula using
-- this identity:
-- @
--   (a | b | c) => (d & e & f)
-- @
-- becomes
-- @
--    a | b | c => d
--    a | b | c => e
--    a | b | c => f
-- @
implicativeNormalForm :: forall m formula term v p f lit. 
                         (Monad m, FirstOrderFormula formula term v p f, Data formula, Literal lit term v p f) =>
                         formula -> NormalT v term m (S.Set (ImplicativeNormalForm lit))
implicativeNormalForm formula =
    do cnf <- clauseNormalForm formula
       let pairs = S.map (S.fold collect (S.empty, S.empty)) cnf :: S.Set (S.Set lit, S.Set lit)
           pairs' = S.flatten (S.map split pairs) :: S.Set (S.Set lit, S.Set lit)
       return (S.map (\ (n,p) -> makeINF n p) pairs')
    -- clauseNormalForm formula >>= return . S.unions . S.map split . map (S.fold collect (S.empty, S.empty))
    where
      collect :: lit -> (S.Set lit, S.Set lit) -> (S.Set lit, S.Set lit)
      collect f (n, p) =
          foldN (\ f' -> (S.insert f' n, p))
                (\ _ -> (n, S.insert f p))
                f
      split :: (S.Set lit, S.Set lit) -> S.Set (S.Set lit, S.Set lit)
      split (lhs, rhs) =
          if any isJust (map fromSkolem (gFind rhs :: [f]))
          then S.map (\ x -> (lhs, S.singleton x)) rhs
          else S.singleton (lhs, rhs)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
