{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Negation
    ( negationNormalForm
    , nnf
    , simplify
    ) where

import Data.Logic.Classes.Combine (Combinable(..), Combine(..), combine, BinOp(..))
import Data.Logic.Classes.Constants (Boolean(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), freeVars, quant, Quant(..), Predicate(..), Pred(..), pApp)
import Data.Logic.Classes.Negate (Negatable(..))
import qualified Data.Set.Extra as S

-- | Simplify and recursively apply nnf.
negationNormalForm :: FirstOrderFormula formula term v p f => formula -> formula
negationNormalForm = nnf . simplify

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
nnf :: FirstOrderFormula formula term v p f => formula -> formula
nnf fm =
    foldFirstOrder nnfQuant nnfCombine (\ _ -> fm) fm
    where
      nnfQuant op v p = quant op v (nnf p)
      nnfCombine ((:~:) p) = foldFirstOrder nnfNotQuant nnfNotCombine (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q
      nnfNotQuant All v p = exists v (nnf ((.~.) p))
      nnfNotQuant Exists v p = for_all v (nnf ((.~.) p))
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

-- |Do a bottom-up recursion to simplify a formula.
simplify :: FirstOrderFormula formula term v p f => formula -> formula
simplify fm =
    foldFirstOrder (\ op v p -> simplify1 (quant op v (simplify p)))
          (\ cm -> case cm of
                     (:~:) p -> simplify1 ((.~.) (simplify p))
                     BinOp p op q -> simplify1 (combine (BinOp (simplify p) op (simplify q))))
          (\ _ -> simplify1 fm)
          fm

-- |Extend psimplify1 to handle quantifiers.  Any quantifier which has
-- no corresponding free occurrences of the quantified variable is
-- eliminated.
simplify1 :: FirstOrderFormula formula term v p f => formula -> formula
simplify1 fm =
    foldFirstOrder (\ _ v p -> if S.member v (freeVars p) then fm else p)
          (\ _ -> psimplify1 fm)
          (\ _ -> psimplify1 fm)
          fm

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
psimplify1 :: forall formula term v p f. FirstOrderFormula formula term v p f => formula -> formula
psimplify1 fm =
    foldFirstOrder (\ _ _ _ -> fm) simplifyCombine (\ _ -> fm) fm
    where
      simplifyCombine ((:~:) f) = foldFirstOrder (\ _ _ _ -> fm) simplifyNotCombine simplifyNotPred f
      simplifyCombine (BinOp l op r) =
          case (pBool l, op, pBool r) of
            (Just True,  (:&:), _)            -> r
            (Just False, (:&:), _)            -> false
            (_,          (:&:), Just True)    -> l
            (_,          (:&:), Just False)   -> false
            (Just True,  (:|:), _)            -> true
            (Just False, (:|:), _)            -> r
            (_,          (:|:), Just True)    -> true
            (_,          (:|:), Just False)   -> l
            (Just True,  (:=>:), _)           -> r
            (Just False, (:=>:), _)           -> true
            (_,          (:=>:), Just True)   -> true
            (_,          (:=>:), Just False)  -> (.~.) l
            (Just True,  (:<=>:), _)          -> r
            (Just False, (:<=>:), _)          -> (.~.) r
            (_,          (:<=>:), Just True)  -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _                                 -> fm
      simplifyNotCombine ((:~:) f) = f
      simplifyNotCombine _ = fm
      simplifyNotPred (Apply pr ts)
          | pr == fromBool False = pApp0 (fromBool True)
          | pr == fromBool True = pApp0 (fromBool False)
          | True = (.~.) (pApp pr ts)
      simplifyNotPred (Constant x) = pApp0 (fromBool (not x))
      simplifyNotPred (Equal t1 t2) = t1 .!=. t2
      simplifyNotPred (NotEqual t1 t2) = t1 .=. t2
      -- Return a Maybe Bool depending upon whether a formula is true,
      -- false, or something else.
      pBool :: formula -> Maybe Bool
      pBool = foldFirstOrder (\ _ _ _ -> Nothing) (\ _ -> Nothing) p
          where p (Apply pr _ts) =
                    if pr == fromBool True
                    then Just True
                    else if pr == fromBool False
                         then Just False
                         else Nothing
                p _ = Nothing
