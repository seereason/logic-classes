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
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Clause
    ( clauseNormalForm
    , trivial
    , cnfTrace
    ) where

import Data.Logic.Normal.Negation (negationNormalForm, nnf, simplify)
import Data.Logic.Normal.Prenex (prenexNormalForm)
import Data.Logic.Normal.Skolem (skolemNormalForm, NormalT)

import Data.List (intersperse)
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), prettyFirstOrder, Predicate(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Literal (Literal(..), prettyLit, fromFirstOrder)
import qualified Data.Set.Extra as Set
import Text.PrettyPrint (Doc, hcat, vcat, text, nest, ($$), brackets, render)

-- |Convert to Skolem Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
clauseNormalForm :: (Monad m, FirstOrderFormula formula term v p f, Literal lit term v p f) =>
       formula -> NormalT v term m (Set.Set (Set.Set lit))
clauseNormalForm fm = skolemNormalForm fm >>= return . simpcnf

cnfTrace :: forall m formula term v p f lit.
            (Monad m, FirstOrderFormula formula term v p f, Literal lit term v p f) =>
            (v -> Doc)
         -> (p -> Doc)
         -> (f -> Doc)
         -> formula
         -> NormalT v term m (String, Set.Set (Set.Set lit))
cnfTrace pv pp pf f =
    do let simplified = simplify f
           pnf = prenexNormalForm f
       snf <- skolemNormalForm f
       cnf <- clauseNormalForm f
       return (render (vcat
                       [text "Original:" $$ nest 2 (prettyFirstOrder pv pp pf 0 f),
                        text "Simplified:" $$ nest 2 (prettyFirstOrder pv pp pf 0 simplified),
                        text "Negation Normal Form:" $$ nest 2 (prettyFirstOrder pv pp pf 0 (negationNormalForm f)),
                        text "Prenex Normal Form:" $$ nest 2 (prettyFirstOrder pv pp pf 0 pnf),
                        text "Skolem Normal Form:" $$ nest 2 (prettyFirstOrder pv pp pf 0 snf),
                        text "Clause Normal Form:" $$ vcat (map prettyClause (fromSS cnf))]), cnf)
    where
      prettyClause (clause :: [lit]) =
          nest 2 . brackets . hcat . intersperse (text ", ") . map (nest 2 . brackets . prettyLit pv pp pf 0) $ clause
      fromSS = (map Set.toList) . Set.toList 

simpcnf :: forall formula term v p f lit. (FirstOrderFormula formula term v p f, Literal lit term v p f) =>
           formula -> Set.Set (Set.Set lit)
simpcnf fm =
    foldFirstOrder (\ _ _ _ -> cjs') (\ _ -> cjs') p fm
    where
      p (Apply pr _ts)
          | pr == fromBool False = Set.empty
          | pr == fromBool True = Set.singleton Set.empty
          | True = cjs'
      p (Equal _ _) = cjs'
      p (NotEqual _ _) = cjs'
      p (Constant _) = cjs'
      -- Discard any clause that is the proper subset of another clause
      cjs' = Set.filter keep cjs
      keep x = not (Set.or (Set.map (Set.isProperSubsetOf x) cjs))
      cjs = Set.filter (not . trivial) (purecnf (nnf fm)) :: Set.Set (Set.Set lit)

-- |Harrison page 59.  Look for complementary pairs in a clause.
trivial :: (Negatable lit, Ord lit) => Set.Set lit -> Bool
trivial lits =
    not . Set.null $ Set.intersection (Set.map (.~.) n) p
    where (n, p) = Set.partition negated lits

-- | CNF: (a | b | c) & (d | e | f)
purecnf :: forall formula term v p f lit. (FirstOrderFormula formula term v p f, Literal lit term v p f) =>
           formula -> Set.Set (Set.Set lit)
purecnf fm = Set.map (Set.map (.~.)) (purednf (nnf ((.~.) fm)))

purednf :: forall formula term v p f lit. (FirstOrderFormula formula term v p f, Literal lit term v p f) =>
           formula -> Set.Set (Set.Set lit)
purednf fm =
    foldFirstOrder (\ _ _ _ -> x) c (\ _ -> x)  fm
    where
      c :: Combination formula -> Set.Set (Set.Set lit)
      c (BinOp p (:&:) q) = Set.distrib (purednf p) (purednf q)
      c (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      c _ = x
      x :: Set.Set (Set.Set lit)
      x = Set.singleton (Set.singleton (fromFirstOrder id id id fm)) :: Set.Set (Set.Set lit)
