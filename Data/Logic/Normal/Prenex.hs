{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Prenex
    ( prenexNormalForm
    ) where

import Data.Logic.Normal.Negation (negationNormalForm)

import Data.Logic.Classes.Combine (Combinable(..), Combine(..), BinOp(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), freeVars, quant, Quant(..), substitute)
import Data.Logic.Classes.Term (Term(var))
import Data.Logic.Classes.Variable (variant)

-- |Convert to Prenex normal form, with all quantifiers at the left.
prenexNormalForm :: (FirstOrderFormula formula term v p f) => formula -> formula
prenexNormalForm = prenex . negationNormalForm

-- |Recursivly apply pullQuants anywhere a quantifier might not be
-- leftmost.
prenex :: (FirstOrderFormula formula term v p f) => formula -> formula 
prenex fm =
    foldFirstOrder q c (\ _ -> fm) fm
    where
      q op x p = quant op x (prenex p)
      c (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      c (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      c _ = fm

-- |Perform transformations to move quantifiers outside of binary
-- operators:
-- 
-- @
--  Formula            Rewrites to
--  (1) ∀x F[x] & G        ∀x    (F[x] & G)
--  (2) ∀x F[x] & ∀x G[x]  ∀x ∀x (F[x] & G[x])
--  (3) ∃x F[x] & G        ∃x    (F[x] & G)
--  (4) ∃x F[x] & ∃x G[x]  ∃x Yz (F[x] & G[z]) -- rename
-- 
--  (5) ∀x F[x] | G        ∀x    (F[x] | G)
--  (6) ∀x F[x] | ∀x G[x]  ∀x ∀z (F[x] | G[z]) -- rename
--  (7) ∃x F[x] | G        ∃x    (F[x] | G)
--  (8) ∃x F[x] | ∃x G[x]  ∃x Yx (F[x] | G[x])
-- @
pullQuants :: forall formula term v p f. (FirstOrderFormula formula term v p f) => formula -> formula
pullQuants fm =
    foldFirstOrder (\ _ _ _ -> fm) pullQuantsCombine (\ _ -> fm) fm
    where
      getQuant = foldFirstOrder (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing)
      pullQuantsCombine ((:~:) _) = fm
      pullQuantsCombine (BinOp l op r) = 
          case (getQuant l, op, getQuant r) of
            (Just (All, vl, l'),    (:&:), Just (All, vr, r'))    -> pullq True  True  fm for_all (.&.) vl vr l' r'
            (Just (Exists, vl, l'), (:|:), Just (Exists, vr, r')) -> pullq True  True  fm exists  (.|.) vl vr l' r'
            (Just (All, vl, l'),    (:&:), _)                     -> pullq True  False fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just (All, vr, r'))    -> pullq False True  fm for_all (.&.) vr vr l  r'
            (Just (All, vl, l'),    (:|:), _)                     -> pullq True  False fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just (All, vr, r'))    -> pullq False True  fm for_all (.|.) vr vr l  r'
            (Just (Exists, vl, l'), (:&:), _)                     -> pullq True  False fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.&.) vr vr l  r'
            (Just (Exists, vl, l'), (:|:), _)                     -> pullq True  False fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: FirstOrderFormula formula term v p f =>
         Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> formula
pullq l r fm mkq op x y p q =
    let z = variant x (freeVars fm)
        p' = if l then substitute x (var z) p else p
        q' = if r then substitute y (var z) q else q
        fm' = pullQuants (op p' q') in
    mkq z fm'
