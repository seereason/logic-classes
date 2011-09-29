{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Data.Logic.Propositional.Normal
    ( negationNormalForm
    , nnf
    , psimplify
    ) where

import Data.Logic.Logic
import Data.Logic.Propositional.Formula

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
