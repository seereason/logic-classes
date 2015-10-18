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
{-# LANGUAGE CPP, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Clause
    ( {- clauseNormalForm
    , cnfTrace -}
    ) where
#if 0
import Data.List as List (intersperse, map)
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Equals (HasEquality, prettyAtomEq)
import Data.Logic.Classes.FirstOrder (IsQuantified(..), prettyFirstOrder)
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Propositional (IsPropositional)
import Data.Logic.Classes.Term (IsTerm)
import Data.Logic.Harrison.Normal (simpcnf')
import Data.Logic.Harrison.Skolem (skolemize, SkolemT, pnf, nnf, simplify)
import Data.Set.Extra as Set (fromSS, Set)
import Text.PrettyPrint (Doc, hcat, vcat, text, nest, ($$), brackets, render)

-- |Convert to Skolem Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
clauseNormalForm :: forall formula atom term v f lit m.
                    (Monad m,
                     IsQuantified formula atom v,
                     IsPropositional formula atom,
                     Atom atom term v,
                     IsTerm term v f,
                     IsLiteral lit atom,
                     Ord formula, Ord lit) =>
                    formula -> SkolemT v term m (Set.Set (Set.Set lit))
clauseNormalForm fm = skolemize id fm >>= return . (simpcnf' :: formula -> Set.Set (Set.Set lit))

cnfTrace :: forall m formula atom term v p f lit.
            (Monad m,
             IsQuantified formula atom v,
             IsPropositional formula atom,
             Atom atom term v,
             HasEquality atom p term,
             IsTerm term v f,
             IsLiteral lit atom,
             Ord formula, Ord lit) =>
            (v -> Doc)
         -> (p -> Doc)
         -> (f -> Doc)
         -> formula
         -> SkolemT v term m (String, Set.Set (Set.Set lit))
cnfTrace pv pp pf f =
    do (snf :: formula) <- skolemize id f
       cnf <- clauseNormalForm f
       return (render (vcat
                       [text "Original:" $$ nest 2 (prettyFirstOrder (prettyAtomEq pv pp pf) pv 0 f),
                        text "Simplified:" $$ nest 2 (prettyFirstOrder (prettyAtomEq pv pp pf) pv 0 (simplify f)),
                        text "Negation Normal Form:" $$ nest 2 (prettyFirstOrder (prettyAtomEq pv pp pf) pv 0 (nnf . simplify $ f)),
                        text "Prenex Normal Form:" $$ nest 2 (prettyFirstOrder (prettyAtomEq pv pp pf) pv 0 (pnf f)),
                        text "Skolem Normal Form:" $$ nest 2 (prettyFirstOrder (prettyAtomEq pv pp pf) pv 0 snf),
                        text "Clause Normal Form:" $$ vcat (List.map prettyClause (fromSS cnf))]), cnf)
    where
      prettyClause (clause :: [lit]) =
          nest 2 . brackets . hcat . intersperse (text ", ") . List.map (nest 2 . brackets . pPrint) $ clause
#endif
