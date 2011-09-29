{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Data.Logic.Propositional.Normal
    ( negationNormalForm
    , clauseNormalForm
    , clauseNormalForm'
    , disjunctiveNormalForm
    , disjunctiveNormalForm'
    ) where

import Data.Logic.Logic
import Data.Logic.Propositional.Formula
import qualified Data.Set.Extra as Set

-- | Simplify and recursively apply nnf.
negationNormalForm :: PropositionalFormula formula atom => formula -> formula
negationNormalForm = nnf . psimplify

-- |Eliminate => and <=> and move negations inwards:
-- 
-- @
-- Formula      Rewrites to
--  P => Q      ~P | Q
--  P <=> Q     (P & Q) | (~P & ~Q)
-- ~∀X P        ∃X ~P
-- ~∃X P        ∀X ~P
-- ~(P & Q)     (~P | ~Q)
-- ~(P | Q)     (~P & ~Q)
-- ~~P  P
-- @
-- 
nnf :: PropositionalFormula formula atom => formula -> formula
nnf fm =
    foldF0 (nnfCombine fm) (\ _ -> fm) fm

nnfCombine :: PropositionalFormula r atom => r -> Combine r -> r
nnfCombine fm ((:~:) p) = foldF0 nnfNotCombine (\ _ -> fm) p
nnfCombine _ (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
nnfCombine _ (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
nnfCombine _ (BinOp p (:&:) q) = nnf p .&. nnf q
nnfCombine _ (BinOp p (:|:) q) = nnf p .|. nnf q

nnfNotCombine :: PropositionalFormula formula atom => Combine formula -> formula
nnfNotCombine ((:~:) p) = nnf p
nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

-- |Do a bottom-up recursion to simplify a propositional formula.
psimplify :: PropositionalFormula formula atom => formula -> formula
psimplify fm =
    foldF0 c a fm
    where
      c ((:~:) p) = psimplify1 ((.~.) (psimplify p))
      c (BinOp p (:&:) q) = psimplify1 (psimplify p .&. psimplify q)
      c (BinOp p (:|:) q) = psimplify1 (psimplify p .|. psimplify q)
      c (BinOp p (:=>:) q) = psimplify1 (psimplify p .=>. psimplify q)
      c (BinOp p (:<=>:) q) = psimplify1 (psimplify p .<=>. psimplify q)
      a _ = fm

-- |Do one step of simplify for propositional formulas:
-- Perform the following transformations everywhere, plus any
-- commuted versions for &, |, and <=>.
-- 
-- @
--  ~False      -> True
--  ~True       -> False
--  True & P    -> P
--  False & P   -> False
--  True | P    -> True
--  False | P   -> P
--  True => P   -> P
--  False => P  -> True
--  P => True   -> P
--  P => False  -> True
--  True <=> P  -> P
--  False <=> P -> ~P
-- @
-- 
psimplify1 :: forall formula atom. PropositionalFormula formula atom => formula -> formula
psimplify1 fm =
    foldF0 simplifyCombine (\ _ -> fm) fm
    where
      simplifyCombine ((:~:) f) = foldF0 simplifyNotCombine simplifyNotAtom f
      simplifyCombine (BinOp l op r) =
          case (asBool l, op, asBool r) of
            (Just True,  (:&:), _)            -> r
            (Just False, (:&:), _)            -> fromBool False
            (_,          (:&:), Just True)    -> l
            (_,          (:&:), Just False)   -> fromBool False
            (Just True,  (:|:), _)            -> fromBool True
            (Just False, (:|:), _)            -> r
            (_,          (:|:), Just True)    -> fromBool True
            (_,          (:|:), Just False)   -> l
            (Just True,  (:=>:), _)           -> r
            (Just False, (:=>:), _)           -> fromBool True
            (_,          (:=>:), Just True)   -> fromBool True
            (_,          (:=>:), Just False)  -> (.~.) l
            (Just True,  (:<=>:), _)          -> r
            (Just False, (:<=>:), _)          -> (.~.) r
            (_,          (:<=>:), Just True)  -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _                                 -> fm
      simplifyNotCombine ((:~:) f) = f
      simplifyNotCombine _ = fm
      simplifyNotAtom x = (.~.) (atomic x)
      -- We don't require an Eq instance, but we do require Ord so that
      -- we can make sets.
      asBool :: formula -> Maybe Bool
      asBool x =
          case compare x (fromBool True) of
            EQ -> Just True
            _ -> case compare x (fromBool False) of
                   EQ -> Just False
                   _ -> Nothing

clauseNormalForm' :: (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
clauseNormalForm' = simp purecnf . negationNormalForm

clauseNormalForm :: forall formula atom. (PropositionalFormula formula atom) => formula -> formula
clauseNormalForm formula =
    case clean (lists cnf) of
      [] -> fromBool True
      xss -> foldr1 (.&.) . map (foldr1 (.|.)) $ xss
    where
      clean = filter (not . null)
      lists = Set.toList . Set.map Set.toList
      cnf = clauseNormalForm' formula

disjunctiveNormalForm :: (PropositionalFormula formula atom) => formula -> formula
disjunctiveNormalForm formula =
    case clean (lists dnf) of
      [] -> fromBool False
      xss -> foldr1 (.|.) . map (foldr1 (.&.)) $ xss
    where
      clean = filter (not . null)
      lists = Set.toList . Set.map Set.toList
      dnf = disjunctiveNormalForm' formula

disjunctiveNormalForm' :: (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
disjunctiveNormalForm' = simp purednf . negationNormalForm

simp :: forall formula atom. (PropositionalFormula formula atom) =>
        (formula -> Set.Set (Set.Set formula)) -> formula -> Set.Set (Set.Set formula)
simp purenf fm =
    case (compare fm (fromBool False), compare fm (fromBool True)) of
      (EQ, _) -> Set.empty
      (_, EQ) -> Set.singleton Set.empty
      _ ->cjs'
    where
      -- Discard any clause that is the proper subset of another clause
      cjs' = Set.filter keep cjs
      keep x = not (Set.or (Set.map (Set.isProperSubsetOf x) cjs))
      cjs = Set.filter (not . trivial) (purenf (nnf fm)) :: Set.Set (Set.Set formula)

-- |Harrison page 59.  Look for complementary pairs in a clause.
trivial :: (Negatable lit, Ord lit) => Set.Set lit -> Bool
trivial lits =
    not . Set.null $ Set.intersection (Set.map (.~.) n) p
    where (n, p) = Set.partition negated lits

-- | CNF: (a | b | c) & (d | e | f)
--purecnf :: forall formula term v p f lit. (FirstOrderFormula formula term v p f, Literal lit term v p f) => formula -> Set.Set (Set.Set lit)
purecnf :: forall formula atom. PropositionalFormula formula atom => formula -> Set.Set (Set.Set formula)
purecnf fm = Set.map (Set.map (.~.)) (purednf (nnf ((.~.) fm)))

purednf :: forall formula atom. (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
purednf fm =
    foldF0 c (\ _ -> x)  fm
    where
      c :: Combine formula -> Set.Set (Set.Set formula)
      c (BinOp p (:&:) q) = Set.distrib (purednf p) (purednf q)
      c (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      c _ = x
      x :: Set.Set (Set.Set formula)
      x = Set.singleton (Set.singleton (convertProp id fm)) :: Set.Set (Set.Set formula)
