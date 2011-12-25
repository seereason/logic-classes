{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Harrison.Prop
    ( eval
    , atoms
    , onAllValuations
    , truthTable
    , tautology
    , unsatisfiable
    , satisfiable
    , rawdnf
    , purednf
    , dnf
    , trivial
    , psimplify
    , nnf
    -- , simpdnf
    , simpcnf
    , positive
    , negative
    , negate
    , distrib
    , list_disj
    , list_conj
    -- previously unexported
    , pSubst
    , dual
    , nenf
    , mkLits
    , allSatValuations
    , dnf0
    , cnf
    ) where

import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..), binop)
import Data.Logic.Classes.Constants (true, false)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Propositional
import Data.Logic.Harrison.Formulas.Propositional (atom_union, on_atoms)
import Data.Logic.Harrison.Lib (fpf, allpairs, setAny)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (negate)

-- ------------------------------------------------------------------------- 
-- Parsing of propositional formulas.                                        
-- ------------------------------------------------------------------------- 

{-
let parse_propvar vs inp =
  match inp with
    p::oinp when p /= "(" -> Atom(P(p)),oinp
  | _ -> failwith "parse_propvar";;

let parse_prop_formula = make_parser
  (parse_formula ((fun _ _ -> failwith ""),parse_propvar) []);;
-}

-- ------------------------------------------------------------------------- 
-- Set this up as default for quotations.                                    
-- ------------------------------------------------------------------------- 

{-
let default_parser = parse_prop_formula;;
-}

-- ------------------------------------------------------------------------- 
-- Printer.                                                                  
-- ------------------------------------------------------------------------- 

{-
let print_propvar prec p = print_string(pname p);;

let print_prop_formula = print_qformula print_propvar;;

#install_printer print_prop_formula;;
-}

-- ------------------------------------------------------------------------- 
-- Interpretation of formulas.                                               
-- ------------------------------------------------------------------------- 

eval :: PropositionalFormula formula atomic => formula -> (atomic -> Bool) -> Bool
eval fm v =
    foldPropositional c a fm
    where
      c FALSE = False
      c TRUE = True
      c ((:~:) p) = not (eval p v)
      c (BinOp p (:&:) q) = eval p v && eval q v
      c (BinOp p (:|:) q) = eval p v || eval q v
      c (BinOp p (:=>:) q) = not (eval p v) || eval q v
      c (BinOp p (:<=>:) q) = eval p v == eval q v
      a x = v x

{-
START_INTERACTIVE;;
eval <<p /\ q ==> q /\ r>>
     (function P"p" -> true | P"q" -> false | P"r" -> true);;

eval <<p /\ q ==> q /\ r>>
     (function P"p" -> true | P"q" -> true | P"r" -> false);;
END_INTERACTIVE;;
-}

-- ------------------------------------------------------------------------- 
-- Return the set of propositional variables in a formula.                   
-- ------------------------------------------------------------------------- 

atoms :: Ord atomic => PropositionalFormula formula atomic => formula -> Set.Set atomic
atoms = atom_union Set.singleton

-- ------------------------------------------------------------------------- 
-- Code to print out truth tables.                                           
-- ------------------------------------------------------------------------- 

onAllValuations :: (Eq a) =>
                   (r -> r -> r)      -- ^ Combine function for result type
                -> ((a -> Bool) -> r) -- ^ The substitution function
                -> (a -> Bool)        -- ^ The default valuation function for atoms not in ps
                -> Set.Set a          -- ^ The variables to vary
                -> r
onAllValuations _ subfn v ps | Set.null ps = subfn v
onAllValuations append subfn v ps =
    case Set.deleteFindMin ps of
      (p, ps') -> append -- Do the valuations of the remaining variables with  set to false
                        (onAllValuations append subfn (\ q -> if q == p then False else v q) ps')
                        -- Do the valuations of the remaining variables with  set to true
                        (onAllValuations append subfn (\ q -> if q == p then True else v q) ps')

type TruthTableRow a = ([(a, Bool)], Bool)

truthTable :: forall formula atomic. (PropositionalFormula formula atomic, Eq atomic, Ord atomic) =>
              formula -> [TruthTableRow atomic]
truthTable fm =
    onAllValuations (++) mkRow (const False) ats
    where
      mkRow :: (atomic -> Bool)         -- The current variable assignment
            -> [TruthTableRow atomic] -- The variable assignments and the formula value
      mkRow v = [(map (\ a -> (a, v a)) (Set.toList ats), eval fm v)]
      ats = atoms fm

-- ------------------------------------------------------------------------- 
-- Recognizing tautologies.                                                  
-- ------------------------------------------------------------------------- 

tautology :: (PropositionalFormula formula atomic, Ord atomic) => formula -> Bool
tautology fm = onAllValuations (&&) (eval fm) (const False) (atoms fm)

-- ------------------------------------------------------------------------- 
-- Related concepts.                                                         
-- ------------------------------------------------------------------------- 


unsatisfiable :: (PropositionalFormula formula atomic, Ord atomic) => formula -> Bool
unsatisfiable fm = tautology ((.~.) fm)

satisfiable :: (PropositionalFormula formula atomic, Ord atomic) => formula -> Bool
satisfiable = not . unsatisfiable

-- ------------------------------------------------------------------------- 
-- Substitution operation.                                                   
-- ------------------------------------------------------------------------- 

-- pSubst :: Ord a => Map.Map a (Formula a) -> Formula a -> Formula a
pSubst :: (PropositionalFormula formula atomic, Ord atomic) => Map.Map atomic formula -> formula -> formula
pSubst subfn fm = on_atoms (\ p -> maybe (atomic p) id (fpf subfn p)) fm

-- ------------------------------------------------------------------------- 
-- Dualization.                                                              
-- ------------------------------------------------------------------------- 

dual :: forall formula atomic. (PropositionalFormula formula atomic) => formula -> formula
dual fm =
    foldPropositional c a fm
    where
      c FALSE = true
      c TRUE = false
      c ((:~:) _) = fm
      c (BinOp p (:&:) q) = dual p .|. dual q
      c (BinOp p (:|:) q) = dual p .&. dual q
      c _ = error "dual: Formula involves connectives ==> or <=>";;
      a atom = atomic atom

-- ------------------------------------------------------------------------- 
-- Routine simplification.                                                   
-- ------------------------------------------------------------------------- 

psimplify1 :: PropositionalFormula r a => r -> r
psimplify1 fm =
    foldPropositional simplifyCombine (\ _ -> fm) fm
    where
      simplifyCombine TRUE = fm
      simplifyCombine FALSE = fm
      simplifyCombine ((:~:) fm') = foldPropositional simplifyNotCombine (\ _ -> fm) fm'
      simplifyCombine (BinOp l op r) =
          case (testBool l, op, testBool r) of
            (Just True,  (:&:), _         ) -> r
            (Just False, (:&:), _         ) -> false
            (_,          (:&:), Just True ) -> l
            (_,          (:&:), Just False) -> false
            (Just True,  (:|:), _         ) -> true
            (Just False, (:|:), _         ) -> r
            (_,          (:|:), Just True ) -> true
            (_,          (:|:), Just False) -> l
            (Just True,  (:=>:), _         ) -> r
            (Just False, (:=>:), _         ) -> true
            (_,          (:=>:), Just True ) -> true
            (_,          (:=>:), Just False) -> (.~.) l
            (Just True,  (:<=>:), _         ) -> r
            (Just False, (:<=>:), _         ) -> (.~.) r
            (_,          (:<=>:), Just True ) -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _ -> fm

      simplifyNotCombine TRUE = false
      simplifyNotCombine FALSE = true
      simplifyNotCombine ((:~:) p) = p
      simplifyNotCombine _ = fm
      testBool = foldPropositional (\ x -> case x of TRUE -> Just True; FALSE -> Just False; _ -> Nothing) (const Nothing)

psimplify :: forall formula atomic. PropositionalFormula formula atomic => formula -> formula
psimplify fm =
    foldPropositional c a fm
    where
      c :: Combination formula -> formula
      c ((:~:) p) = psimplify1 ((.~.) (psimplify p))
      c (BinOp p op q) = psimplify1 (binop (psimplify p) op (psimplify q))
      c _ = fm
      a _ = fm

-- ------------------------------------------------------------------------- 
-- Some operations on literals.                                              
-- ------------------------------------------------------------------------- 

negative :: PropositionalFormula formula atomic => formula -> Bool
negative lit =
    foldPropositional c a lit
    where
      c ((:~:) _) = True
      c _ = False
      a _ = False

positive :: PropositionalFormula formula atomic => formula -> Bool
positive = not . negative

negate :: PropositionalFormula formula atomic => formula -> formula
negate lit =
    foldPropositional c a lit
    where
      c ((:~:) p) = p
      c _ = (.~.) lit
      a _ = (.~.) lit

-- ------------------------------------------------------------------------- 
-- Negation normal form.                                                     
-- ------------------------------------------------------------------------- 

nnf' :: PropositionalFormula formula atomic => formula -> formula
nnf' fm =
    foldPropositional {-nnfQuant-} nnfCombine (\ _ -> fm) fm
    where
      -- nnfQuant op v p = quant op v (nnf' p)
      nnfCombine TRUE = true
      nnfCombine FALSE = false
      nnfCombine ((:~:) p) = foldPropositional {-nnfNotQuant-} nnfNotCombine (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf' ((.~.) p) .|. (nnf' q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf' p .&. nnf' q) .|. (nnf' ((.~.) p) .&. nnf' ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf' p .&. nnf' q
      nnfCombine (BinOp p (:|:) q) = nnf' p .|. nnf' q
      -- nnfNotQuant All v p = exists v (nnf' ((.~.) p))
      -- nnfNotQuant Exists v p = for_all v (nnf' ((.~.) p))
      nnfNotCombine TRUE = false
      nnfNotCombine FALSE = true
      nnfNotCombine ((:~:) p) = nnf' p
      nnfNotCombine (BinOp p (:&:) q) = nnf' ((.~.) p) .|. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf' ((.~.) p) .&. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf' p .&. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf' p .&. nnf' ((.~.) q)) .|. nnf' ((.~.) p) .&. nnf' q

-- ------------------------------------------------------------------------- 
-- Roll in simplification.                                                   
-- ------------------------------------------------------------------------- 

nnf :: PropositionalFormula formula atomic => formula -> formula
nnf = nnf' . psimplify

-- ------------------------------------------------------------------------- 
-- Simple negation-pushing when we don't care to distinguish occurrences.    
-- ------------------------------------------------------------------------- 

nenf' :: PropositionalFormula formula atomic => formula -> formula
nenf' fm =
    foldPropositional nenfCombine (\ _ -> fm) fm
    where
      nenfCombine ((:~:) p) = foldPropositional nenfNotCombine (\ _ -> fm) p
      nenfCombine (BinOp p (:&:) q) = nenf' p .|. nenf' q
      nenfCombine (BinOp p (:|:) q) = nenf' p .|. nenf' q
      nenfCombine (BinOp p (:=>:) q) = nenf' ((.~.) p) .|. nenf' q
      nenfCombine (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' q
      nenfCombine _ = fm
      nenfNotCombine ((:~:) p) = p
      nenfNotCombine (BinOp p (:&:) q) = nenf' ((.~.) p) .|. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:|:) q) = nenf' ((.~.) p) .&. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:=>:) q) = nenf' p .&. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' ((.~.) q) -- really?  how is this asymmetrical?
      nenfNotCombine _ = fm

nenf :: PropositionalFormula formula atomic => formula -> formula
nenf = nenf' . psimplify

-- ------------------------------------------------------------------------- 
-- Disjunctive normal form (DNF) via truth tables.                           
-- ------------------------------------------------------------------------- 

list_conj :: (PropositionalFormula formula atomic, Ord formula) => Set.Set formula -> formula
list_conj l = maybe true (\ (x, xs) -> Set.fold (.&.) x xs) (Set.minView l)

list_disj :: PropositionalFormula formula atomic => Set.Set formula -> formula
list_disj l = maybe false (\ (x, xs) -> Set.fold (.|.) x xs) (Set.minView l)

mkLits :: (PropositionalFormula formula atomic, Ord formula) =>
          Set.Set formula -> (atomic -> Bool) -> formula
mkLits pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

allSatValuations :: Eq a => ((a -> Bool) -> Bool) -> (a -> Bool) -> Set.Set a -> [a -> Bool]
allSatValuations subfn v pvs =
    case Set.minView pvs of
      Nothing -> if subfn v then [v] else []
      Just (p, ps) -> (allSatValuations subfn (\ q -> if q == p then False else v p) ps) ++
                      (allSatValuations subfn (\ q -> if q == p then True else v p) ps)

dnf0 :: forall formula atomic. (PropositionalFormula formula atomic, Ord atomic, Ord formula) => formula -> formula
dnf0 fm =
    list_disj (Set.fromList (map (mkLits (Set.map atomic pvs)) satvals))
    where
      satvals = allSatValuations (eval fm) (const False) pvs
      pvs = atoms fm

-- ------------------------------------------------------------------------- 
-- DNF via distribution.                                                     
-- ------------------------------------------------------------------------- 

distrib :: PropositionalFormula formula atomic => formula -> formula
distrib fm =
    foldPropositional c a fm
    where
      c (BinOp p (:&:) s) =
          foldPropositional c' a s
          where c' (BinOp q (:|:) r) = distrib (p .&. q) .|. distrib (p .&. r)
                c' _ =
                    foldPropositional c'' a p
                    where c'' (BinOp q (:|:) r) = distrib (q .&. s) .|. distrib (r .&. s)
                          c'' _ = fm
      c _ = fm
      a _ = fm

rawdnf :: PropositionalFormula formula atomic => formula -> formula
rawdnf fm =
    foldPropositional c a fm
    where
      c (BinOp p (:&:) q) = distrib (rawdnf p .&. rawdnf q)
      c (BinOp p (:|:) q) = rawdnf p .|. rawdnf q
      c _ = fm
      a _ = fm

-- ------------------------------------------------------------------------- 
-- A version using a list representation.                                    
-- ------------------------------------------------------------------------- 

distrib' :: (Eq formula, Ord formula) => Set.Set (Set.Set formula) -> Set.Set (Set.Set formula) -> Set.Set (Set.Set formula)
distrib' s1 s2 = allpairs (Set.union) s1 s2

purednf :: (PropositionalFormula formula atomic, Ord formula) => formula -> Set.Set (Set.Set formula)
purednf fm =
    foldPropositional c a fm
    where
      c (BinOp p (:&:) q) = distrib' (purednf p) (purednf q)
      c (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      c _ = Set.singleton (Set.singleton fm)
      a _ = Set.singleton (Set.singleton fm)

-- ------------------------------------------------------------------------- 
-- Filtering out trivial disjuncts (in this guise, contradictory).           
-- ------------------------------------------------------------------------- 

trivial :: (PropositionalFormula formula atomic, Ord formula) => Set.Set formula -> Bool
trivial lits =
    not . Set.null $ Set.intersection neg (Set.map (.~.) pos)
    where (pos, neg) = Set.partition positive lits

-- ------------------------------------------------------------------------- 
-- With subsumption checking, done very naively (quadratic).                 
-- ------------------------------------------------------------------------- 

simpdnf :: forall formula atomic.  (PropositionalFormula formula atomic, Eq formula, Ord formula) => formula -> Set.Set (Set.Set formula)
simpdnf fm =
    foldPropositional c a fm
    where
      c :: Combination formula -> Set.Set (Set.Set formula)
      c FALSE = Set.empty
      c TRUE = Set.singleton Set.empty
      c _ = Set.filter (\ d -> not (setAny (\ d' -> Set.isProperSubsetOf d' d) djs)) djs
          where djs = Set.filter (not . trivial) (purednf (nnf fm))
      a :: atomic -> Set.Set (Set.Set formula)
      a _ = Set.singleton (Set.singleton fm)

-- ------------------------------------------------------------------------- 
-- Mapping back to a formula.                                                
-- ------------------------------------------------------------------------- 

dnf :: (PropositionalFormula formula atomic, Ord formula) => formula -> formula
dnf fm = list_disj (Set.map list_conj (simpdnf fm))

-- ------------------------------------------------------------------------- 
-- Conjunctive normal form (CNF) by essentially the same code.               
-- ------------------------------------------------------------------------- 

purecnf :: (PropositionalFormula formula atomic, Ord formula) => formula -> Set.Set (Set.Set formula)
purecnf fm = Set.map (Set.map (psimplify . (.~.))) (purednf (nnf ((.~.) fm)))

simpcnf :: (PropositionalFormula formula atomic, Ord formula) =>
           formula -> Set.Set (Set.Set formula)
simpcnf fm =
    foldPropositional c a fm
    where
      c FALSE = Set.singleton Set.empty
      c TRUE = Set.empty
      c _ =
          -- Discard any clause that is the proper subset of another clause
          Set.filter (\ cj -> not (setAny (\ c' -> Set.isProperSubsetOf c' cj) cjs)) cjs
          where cjs = Set.filter (not . trivial) (purecnf fm)
      a _ = Set.singleton (Set.singleton fm)

cnf :: (PropositionalFormula formula atomic, Ord formula) => formula -> formula
cnf fm = list_conj (Set.map list_disj (simpcnf fm))
