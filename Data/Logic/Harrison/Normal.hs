{-# OPTIONS_GHC -Wall #-}
-- | Versions of the normal form functions in Prop for FirstOrderFormula.
module Data.Logic.Harrison.Normal where

import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (true, false)
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Harrison.Skolem (nnf, simplify)
import Data.Logic.Harrison.Lib (setAny, allpairs)
import qualified Data.Set as Set

list_conj :: (FirstOrderFormula fof atomic v, Ord fof) => Set.Set fof -> fof
list_conj l = maybe true (\ (x, xs) -> Set.fold (.&.) x xs) (Set.minView l)

list_disj :: (FirstOrderFormula fof atomic v, Ord fof) => Set.Set fof -> fof
list_disj l = maybe false (\ (x, xs) -> Set.fold (.|.) x xs) (Set.minView l)

-- ------------------------------------------------------------------------- 
-- Some operations on literals.                                              
-- ------------------------------------------------------------------------- 

negative :: FirstOrderFormula fof atomic v => fof -> Bool
negative lit =
    foldFirstOrder qu co pr lit
    where
      qu _ _ _ = False
      co ((:~:) _) = True
      co _ = False
      pr _ = False

positive :: FirstOrderFormula fof atomic v => fof -> Bool
positive = not . negative

negate :: FirstOrderFormula fof atomic v => fof -> fof
negate lit =
    foldFirstOrder qu co pr lit
    where
      qu _ _ _ = (.~.) lit
      co ((:~:) p) = p
      co _ = (.~.) lit
      pr _ = (.~.) lit

-- ------------------------------------------------------------------------- 
-- A version using a list representation.                                    
-- ------------------------------------------------------------------------- 

distrib' :: (Eq formula, Ord formula) => Set.Set (Set.Set formula) -> Set.Set (Set.Set formula) -> Set.Set (Set.Set formula)
distrib' s1 s2 = allpairs (Set.union) s1 s2

purednf :: (FirstOrderFormula fof atomic v, Ord fof) => fof -> Set.Set (Set.Set fof)
purednf fm =
    foldFirstOrder qu co pr fm
    where
      qu _ _ _ = Set.singleton (Set.singleton fm)
      co (BinOp p (:&:) q) = distrib' (purednf p) (purednf q)
      co (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      co _ = Set.singleton (Set.singleton fm)
      pr _ = Set.singleton (Set.singleton fm)

-- ------------------------------------------------------------------------- 
-- Filtering out trivial disjuncts (in this guise, contradictory).           
-- ------------------------------------------------------------------------- 

trivial :: (FirstOrderFormula fof atomic v, Ord fof) => Set.Set fof -> Bool
trivial lits =
    not . Set.null $ Set.intersection neg (Set.map (.~.) pos)
    where (pos, neg) = Set.partition positive lits

-- ------------------------------------------------------------------------- 
-- With subsumption checking, done very naively (quadratic).                 
-- ------------------------------------------------------------------------- 

simpdnf :: (FirstOrderFormula fof atomic v, Eq fof, Ord fof) => fof -> Set.Set (Set.Set fof)
simpdnf fm =
    foldFirstOrder qu co pr fm
    where
      qu _ _ _ = def
      co FALSE = Set.empty
      co TRUE = Set.singleton Set.empty
      co _ = def
      pr _ = Set.singleton (Set.singleton fm)
      def =
          Set.filter (\ d -> not (setAny (\ d' -> Set.isProperSubsetOf d' d) djs)) djs
          where djs = Set.filter (not . trivial) (purednf (nnf fm))

-- ------------------------------------------------------------------------- 
-- Conjunctive normal form (CNF) by essentially the same code.               
-- ------------------------------------------------------------------------- 

purecnf :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Ord fof) => fof -> Set.Set (Set.Set fof)
purecnf fm = Set.map (Set.map (simplify . (.~.))) (purednf (nnf ((.~.) fm)))

simpcnf :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Ord formula) => formula -> Set.Set (Set.Set formula)
simpcnf fm =
    foldFirstOrder qu co pr fm
    where
      qu _ _ _ = def
      co FALSE = Set.singleton Set.empty
      co TRUE = Set.empty
      co _ = def
      pr _ = Set.singleton (Set.singleton fm)
      def =
          -- Discard any clause that is the proper subset of another clause
          Set.filter (\ cj -> not (setAny (\ c' -> Set.isProperSubsetOf c' cj) cjs)) cjs
          where cjs = Set.filter (not . trivial) (purecnf fm)


cnf :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Ord fof) => fof -> fof
cnf fm = list_conj (Set.map list_disj (simpcnf fm))

distrib :: (FirstOrderFormula fof atomic v) => fof -> fof
distrib fm =
    foldFirstOrder qu co pr fm
    where
      co (BinOp p (:&:) s) =
          foldFirstOrder qu co' pr s
          where co' (BinOp q (:|:) r) = distrib (p .&. q) .|. distrib (p .&. r)
                co' _ =
                    foldFirstOrder qu co'' pr p
                    where co'' (BinOp q (:|:) r) = distrib (q .&. s) .|. distrib (r .&. s)
                          co'' _ = fm
      co _ = fm
      pr _ = fm
      qu _ _ _ = fm
