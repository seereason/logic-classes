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
import Logic.Logic
import Logic.Monad (NormalT)
import qualified Logic.Set as S
import Text.PrettyPrint (hcat, vcat, text, nest, ($$), brackets, render)

-- | Simplify and recursively apply nnf.
negationNormalForm :: FirstOrderLogic formula term v p f => formula -> formula
negationNormalForm = nnf . simplify

-- |Convert to Prenex normal form, with all quantifiers at the left.
prenexNormalForm :: (FirstOrderLogic formula term v p f) => formula -> formula
prenexNormalForm = prenex . negationNormalForm

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolemNormalForm f = askolemize f >>= return . specialize . prenexNormalForm

-- |Convert to Skolem Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
clauseNormalForm :: (Monad m, FirstOrderLogic formula term v p f, Literal formula) =>
       formula -> NormalT v term m (S.Set (S.Set formula))
clauseNormalForm fm = skolemNormalForm fm >>= return . simpcnf

cnfTrace :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Pretty v, Pretty p, Pretty f) =>
            formula -> NormalT v term m String
cnfTrace f =
    do let simplified = simplify f
           pnf = prenexNormalForm f
       snf <- skolemNormalForm f
       cnf <- clauseNormalForm f
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
implicativeNormalForm :: forall m formula term v p f. 
                         (Monad m, FirstOrderLogic formula term v p f, Literal formula, Data formula) =>
                         formula -> NormalT v term m [([formula], [formula])]
implicativeNormalForm formula =
    clauseNormalForm formula >>= return . concatMap split . map (imply . foldl collect ([], [])) . map S.toList . S.toList
    where
      collect :: ([formula], [formula]) -> formula -> ([formula], [formula])
      collect (n, p) f =
          foldF (\ _ _ _ -> error "collect 1")
                (\ cm -> case cm of
                           ((:~:) f') -> (f' : n, p)
                           _ -> error "collect 2")
                (\ _ -> (n, f : p))
                f
      imply :: ([formula], [formula]) -> ([formula], [formula])
      imply (n, p) = (reverse n, reverse p)
      split :: ([formula], [formula]) -> [([formula], [formula])]
      split (lhs, rhs) =
          if any isJust (map fromSkolem (gFind rhs :: [f]))
          then map (\ x -> (lhs, [x])) rhs
          else [(lhs, rhs)]

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
