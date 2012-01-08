{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
-- | Versions of the normal form functions in Prop for FirstOrderFormula.
module Data.Logic.Harrison.Normal
    ( trivial
    , simpdnf
    , simpcnf
    , simpcnf'
    ) where

import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Equals (AtomEq(foldAtomEq), fromAtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Literal (Literal, fromFirstOrder)
import Data.Logic.Classes.Negate (Negatable, negated, (.~.))
import Data.Logic.Classes.Term (Term)
import Data.Logic.Harrison.Lib (setAny, allpairs)
import Data.Logic.Harrison.Skolem (nnf, simplify)
import qualified Data.Set.Extra as Set
import Prelude hiding (negate)

-- ------------------------------------------------------------------------- 
-- A version using a list representation.  (dsf: now set)
-- ------------------------------------------------------------------------- 

distrib' :: (Eq formula, Ord formula) => Set.Set (Set.Set formula) -> Set.Set (Set.Set formula) -> Set.Set (Set.Set formula)
distrib' s1 s2 = allpairs (Set.union) s1 s2

purednf :: (FirstOrderFormula fof atom v, Ord fof) => fof -> Set.Set (Set.Set fof)
purednf fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ _ _ = Set.singleton (Set.singleton fm)
      co (BinOp p (:&:) q) = distrib' (purednf p) (purednf q)
      co (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      co _ = Set.singleton (Set.singleton fm)
      tf = Set.singleton . Set.singleton . fromBool
      at _ = Set.singleton (Set.singleton fm)

purednf' :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Ord lit) =>
           formula -> Set.Set (Set.Set lit)
purednf' fm =
    foldFirstOrder (\ _ _ _ -> x) co (\ _ -> x) (\ _ -> x)  fm
    where
      co :: Combination formula -> Set.Set (Set.Set lit)
      co (BinOp p (:&:) q) = Set.distrib (purednf' p) (purednf' q)
      co (BinOp p (:|:) q) = Set.union (purednf' p) (purednf' q)
      co _ = x
      x :: Set.Set (Set.Set lit)
      x = Set.singleton (Set.singleton (fromFirstOrder (fromAtomEq id id id) id fm)) :: Set.Set (Set.Set lit)

-- ------------------------------------------------------------------------- 
-- Filtering out trivial disjuncts (in this guise, contradictory).           
-- ------------------------------------------------------------------------- 

trivial :: (Negatable lit, Ord lit) => Set.Set lit -> Bool
trivial lits =
    not . Set.null $ Set.intersection neg (Set.map (.~.) pos)
    where (neg, pos) = Set.partition negated lits

-- ------------------------------------------------------------------------- 
-- With subsumption checking, done very naively (quadratic).                 
-- ------------------------------------------------------------------------- 

simpdnf :: (FirstOrderFormula fof atom v, Eq fof, Ord fof) => fof -> Set.Set (Set.Set fof)
simpdnf fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ _ _ = def
      co _ = def
      tf False = Set.empty
      tf True = Set.singleton Set.empty
      at _ = Set.singleton (Set.singleton fm)
      def = Set.filter keep djs
      keep x = not (setAny (`Set.isProperSubsetOf` x) djs)
      djs = Set.filter (not . trivial) (purednf (nnf fm))

-- ------------------------------------------------------------------------- 
-- Conjunctive normal form (CNF) by essentially the same code.               
-- ------------------------------------------------------------------------- 

purecnf :: (FirstOrderFormula fof atom v, Formula atom term v, AtomEq atom p term, Term term v f, Ord fof) => fof -> Set.Set (Set.Set fof)
purecnf fm = Set.map (Set.map (simplify . (.~.))) (purednf (nnf ((.~.) fm)))

-- | CNF: (a | b | c) & (d | e | f)
purecnf' :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Eq lit, Ord lit) =>
           formula -> Set.Set (Set.Set lit)
purecnf' fm = Set.map (Set.map (.~.)) (purednf' (nnf ((.~.) fm)))

simpcnf :: (FirstOrderFormula formula atom v, Formula atom term v, AtomEq atom p term, Term term v f, Ord formula) => formula -> Set.Set (Set.Set formula)
simpcnf fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ _ _ = def
      co _ = def
      tf False = Set.singleton Set.empty
      tf True = Set.empty
      at x = Set.singleton (Set.singleton (atomic x))
      -- Discard any clause that is the proper subset of another clause
      def = Set.filter keep cjs
      keep x = not (setAny (`Set.isProperSubsetOf` x) cjs)
      cjs = Set.filter (not . trivial) (purecnf fm)

{-
cnf :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Ord fof) => fof -> fof
cnf fm = list_conj (Set.map list_disj (simpcnf fm))

distrib :: (FirstOrderFormula fof atomic v) => fof -> fof
distrib fm =
    foldFirstOrder qu co tf at fm
    where
      co (BinOp p (:&:) s) =
          foldFirstOrder qu co' tf at s
          where co' (BinOp q (:|:) r) = distrib (p .&. q) .|. distrib (p .&. r)
                co' _ =
                    foldFirstOrder qu co'' tf at p
                    where co'' (BinOp q (:|:) r) = distrib (q .&. s) .|. distrib (r .&. s)
                          co'' _ = fm
      co _ = fm
      tf _ = fm
      at _ = fm
      qu _ _ _ = fm
-}

-- Alternative versions, these should be merged

simpcnf' :: forall formula atom term v p f lit. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom v, Ord lit, Eq p, Constants p) =>
           formula -> Set.Set (Set.Set lit)
simpcnf' fm =
    foldFirstOrder (\ _ _ _ -> cjs') co tf at fm
    where
      co _ = cjs'
      at = foldAtomEq (\ _ _ -> cjs') tf (\ _ _ -> cjs')
      tf False = Set.singleton Set.empty
      tf True = Set.empty
      -- Discard any clause that is the proper subset of another clause
      cjs' = Set.filter keep cjs
      keep x = not (Set.or (Set.map (`Set.isProperSubsetOf` x) cjs))
      cjs = Set.filter (not . trivial) (purecnf' (nnf fm)) :: Set.Set (Set.Set lit)
