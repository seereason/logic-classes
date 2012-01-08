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
    , cnfTrace
    ) where

import Data.List (intersperse)
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Equals (AtomEq(foldAtomEq))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.FirstOrderEq (prettyFirstOrderEq, prettyLitEq, fromFirstOrderEq)
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Term (Term)
import Data.Logic.Harrison.Normal (trivial)
import Data.Logic.Harrison.Skolem (skolemNormalForm, SkolemT, pnf, nnf, simplify)
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
clauseNormalForm :: (Monad m, FirstOrderFormula formula atom v, Formula atom term v, AtomEq atom p term, Term term v f, Literal lit atom v, Eq formula, Ord lit, Constants p, Eq p) =>
       formula -> SkolemT v term m (Set.Set (Set.Set lit))
clauseNormalForm fm = skolemNormalForm fm >>= return . simpcnf

cnfTrace :: forall m formula atom term v p f lit.
            (Monad m, FirstOrderFormula formula atom v, Formula atom term v, AtomEq atom p term, Term term v f, Literal lit atom v, Eq formula, Ord lit, Constants p, Eq p) =>
            (v -> Doc)
         -> (p -> Doc)
         -> (f -> Doc)
         -> formula
         -> SkolemT v term m (String, Set.Set (Set.Set lit))
cnfTrace pv pp pf f =
    do snf <- skolemNormalForm f
       cnf <- clauseNormalForm f
       return (render (vcat
                       [text "Original:" $$ nest 2 (prettyFirstOrderEq pv pp pf 0 f),
                        text "Simplified:" $$ nest 2 (prettyFirstOrderEq pv pp pf 0 (simplify f)),
                        text "Negation Normal Form:" $$ nest 2 (prettyFirstOrderEq pv pp pf 0 (nnf . simplify $ f)),
                        text "Prenex Normal Form:" $$ nest 2 (prettyFirstOrderEq pv pp pf 0 (pnf f)),
                        text "Skolem Normal Form:" $$ nest 2 (prettyFirstOrderEq pv pp pf 0 snf),
                        text "Clause Normal Form:" $$ vcat (map prettyClause (fromSS cnf))]), cnf)
    where
      prettyClause (clause :: [lit]) =
          nest 2 . brackets . hcat . intersperse (text ", ") . map (nest 2 . brackets . prettyLitEq pv pp pf 0) $ clause
      fromSS = (map Set.toList) . Set.toList 

simpcnf :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Ord lit, Eq p, Constants p) =>
           formula -> Set.Set (Set.Set lit)
simpcnf fm =
    foldFirstOrder (\ _ _ _ -> cjs') co tf at fm
    where
      co _ = cjs'
      at = foldAtomEq (\ _ _ -> cjs') tf (\ _ _ -> cjs')
      tf False = Set.singleton Set.empty
      tf True = Set.empty
      -- Discard any clause that is the proper subset of another clause
      cjs' = Set.filter keep cjs
      keep x = not (Set.or (Set.map (`Set.isProperSubsetOf` x) cjs))
      cjs = Set.filter (not . trivial) (purecnf (nnf fm)) :: Set.Set (Set.Set lit)

-- | CNF: (a | b | c) & (d | e | f)
purecnf :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Eq lit, Ord lit) =>
           formula -> Set.Set (Set.Set lit)
purecnf fm = Set.map (Set.map (.~.)) (purednf (nnf ((.~.) fm)))

purednf :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Ord lit) =>
           formula -> Set.Set (Set.Set lit)
purednf fm =
    foldFirstOrder (\ _ _ _ -> x) co (\ _ -> x) (\ _ -> x)  fm
    where
      co :: Combination formula -> Set.Set (Set.Set lit)
      co (BinOp p (:&:) q) = Set.distrib (purednf p) (purednf q)
      co (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      co _ = x
      x :: Set.Set (Set.Set lit)
      x = Set.singleton (Set.singleton (fromFirstOrderEq id id id fm)) :: Set.Set (Set.Set lit)
