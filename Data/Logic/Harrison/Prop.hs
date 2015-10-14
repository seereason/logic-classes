{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Harrison.Prop
#if 1
    ( module Prop
    ) where

import Prop
#else
    ( eval
    , atoms
    , onAllValuations
    , TruthTable
    , TruthTableRow
    , truthTable
    , tautology
    , unsatisfiable
    , satisfiable
    , rawdnf
    , purednf
    , dnf
    , dnf'
    , trivial
    , psimplify
    , nnf
    , simpdnf
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
    , cnf'
    ) where

import Data.Bool (bool)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..), binop)
import Data.Logic.Classes.Constants (HasBoolean(fromBool, asBool), true, false)
import Data.Logic.Classes.Formula (IsFormula(atomic))
import Data.Logic.Classes.Literal (IsLiteral(foldLiteral) {-, toPropositional-})
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Propositional
import Data.Logic.Harrison.Formulas.Propositional (atom_union, on_atoms)
import Data.Logic.Harrison.Lib (fpf, setAny)
import qualified Data.Logic.Harrison.Lib as Lib (distrib)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (negate)

-- type Map a = Map.Map a Bool
-- m0 = Map.empty
-- ins :: forall a. Ord a => a -> Bool -> Map a -> Map a
-- ins = Map.insert
-- m ! k = Map.findWithDefault False k m

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

eval :: (IsPropositional formula atomic, Ord atomic) => formula -> Map.Map atomic Bool -> Bool
eval fm v =
    foldPropositional co id at fm
    where
      co ((:~:) p) = not (eval p v)
      co (BinOp p (:&:) q) = eval p v && eval q v
      co (BinOp p (:|:) q) = eval p v || eval q v
      co (BinOp p (:=>:) q) = not (eval p v) || eval q v
      co (BinOp p (:<=>:) q) = eval p v == eval q v
      at x = Map.findWithDefault False x v

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

atoms :: Ord atomic => IsPropositional formula atomic => formula -> Set.Set atomic
atoms = atom_union Set.singleton

-- ------------------------------------------------------------------------- 
-- Code to print out truth tables.                                           
-- ------------------------------------------------------------------------- 

onAllValuations :: (Ord a) =>
                   (r -> r -> r)         -- ^ Combine function for result type
                -> (Map.Map a Bool -> r) -- ^ The substitution function
                -> Map.Map a Bool        -- ^ The default valuation function for atoms not in ps
                -> Set.Set a             -- ^ The variables to vary
                -> r
onAllValuations _ subfn v ps | Set.null ps = subfn v
onAllValuations append subfn v ps =
    case Set.minView ps of
      Nothing -> error "onAllValuations"
      Just (p, ps') ->
          append -- Do the valuations of the remaining variables with  set to false
                 (onAllValuations append subfn (Map.insert p False v) ps')
                 -- Do the valuations of the remaining variables with  set to true
                 (onAllValuations append subfn (Map.insert p True v) ps')

type TruthTableRow = ([Bool], Bool)
type TruthTable a = ([a], [TruthTableRow])

truthTable :: forall formula atom. (IsPropositional formula atom, Eq atom, Ord atom) =>
              formula -> TruthTable atom
truthTable fm =
    (atl, onAllValuations (++) mkRow Map.empty ats)
    where
      mkRow :: Map.Map atom Bool      -- ^ The current variable assignment
            -> [TruthTableRow]          -- ^ The variable assignments and the formula value
      mkRow v = [(map (\ k -> Map.findWithDefault False k v) atl, eval fm v)]
      atl = Set.toAscList ats
      ats = atoms fm

-- ------------------------------------------------------------------------- 
-- Recognizing tautologies.                                                  
-- ------------------------------------------------------------------------- 

tautology :: (IsPropositional formula atomic, Ord atomic) => formula -> Bool
tautology fm = onAllValuations (&&) (eval fm) Map.empty (atoms fm)

-- ------------------------------------------------------------------------- 
-- Related concepts.                                                         
-- ------------------------------------------------------------------------- 


unsatisfiable :: (IsPropositional formula atomic, Ord atomic) => formula -> Bool
unsatisfiable fm = tautology ((.~.) fm)

satisfiable :: (IsPropositional formula atomic, Ord atomic) => formula -> Bool
satisfiable = not . unsatisfiable

-- ------------------------------------------------------------------------- 
-- Substitution operation.                                                   
-- ------------------------------------------------------------------------- 

-- pSubst :: Ord a => Map.Map a (Formula a) -> Formula a -> Formula a
pSubst :: (IsPropositional formula atomic, Ord atomic) => Map.Map atomic formula -> formula -> formula
pSubst subfn fm = on_atoms (\ p -> maybe (atomic p) id (fpf subfn p)) fm

-- ------------------------------------------------------------------------- 
-- Dualization.                                                              
-- ------------------------------------------------------------------------- 

dual :: forall formula atomic. (IsPropositional formula atomic) => formula -> formula
dual fm =
    foldPropositional co (fromBool . not) at fm
    where
      co ((:~:) _) = fm
      co (BinOp p (:&:) q) = dual p .|. dual q
      co (BinOp p (:|:) q) = dual p .&. dual q
      co _ = error "dual: Formula involves connectives ==> or <=>";;
      at = atomic

-- ------------------------------------------------------------------------- 
-- Routine simplification.                                                   
-- ------------------------------------------------------------------------- 

psimplify1 :: (IsPropositional r a, Eq r) => r -> r
psimplify1 fm =
    foldPropositional simplifyCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      simplifyCombine ((:~:) fm') = foldPropositional simplifyNotCombine (fromBool . not) (\ _ -> fm) fm'
      simplifyCombine (BinOp l op r) =
          case (asBool l, op, asBool r) of
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

      simplifyNotCombine ((:~:) p) = p
      simplifyNotCombine _ = fm

psimplify :: forall formula atomic. (IsPropositional formula atomic, Eq formula) => formula -> formula
psimplify fm =
    foldPropositional c (\ _ -> fm) (\ _ -> fm) fm
    where
      c :: Combination formula -> formula
      c ((:~:) p) = psimplify1 ((.~.) (psimplify p))
      c (BinOp p op q) = psimplify1 (binop (psimplify p) op (psimplify q))

-- ------------------------------------------------------------------------- 
-- Some operations on literals.                                              
-- ------------------------------------------------------------------------- 

negative :: forall lit atom. IsLiteral lit atom => lit -> Bool
negative lit =
    foldLiteral neg tf a lit
    where
      neg _ = True
      tf = not
      a _ = False

positive :: IsLiteral lit atom => lit -> Bool
positive = not . negative

negate :: IsPropositional formula atomic => formula -> formula
negate lit =
    foldPropositional c (fromBool . not) a lit
    where
      c ((:~:) p) = p
      c _ = (.~.) lit
      a _ = (.~.) lit

-- ------------------------------------------------------------------------- 
-- Negation normal form.                                                     
-- ------------------------------------------------------------------------- 

nnf' :: IsPropositional formula atomic => formula -> formula
nnf' fm =
    foldPropositional nnfCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      nnfCombine ((:~:) p) = foldPropositional nnfNotCombine (fromBool . not) (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf' ((.~.) p) .|. (nnf' q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf' p .&. nnf' q) .|. (nnf' ((.~.) p) .&. nnf' ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf' p .&. nnf' q
      nnfCombine (BinOp p (:|:) q) = nnf' p .|. nnf' q
      nnfNotCombine ((:~:) p) = nnf' p
      nnfNotCombine (BinOp p (:&:) q) = nnf' ((.~.) p) .|. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf' ((.~.) p) .&. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf' p .&. nnf' ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf' p .&. nnf' ((.~.) q)) .|. nnf' ((.~.) p) .&. nnf' q

-- ------------------------------------------------------------------------- 
-- Roll in simplification.                                                   
-- ------------------------------------------------------------------------- 

nnf :: (IsPropositional formula atomic, Eq formula) => formula -> formula
nnf = nnf' . psimplify

-- ------------------------------------------------------------------------- 
-- Simple negation-pushing when we don't care to distinguish occurrences.    
-- ------------------------------------------------------------------------- 

nenf' :: IsPropositional formula atomic => formula -> formula
nenf' fm =
    foldPropositional nenfCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      nenfCombine ((:~:) p) = foldPropositional nenfNotCombine (\ _ -> fm) (\ _ -> fm) p
      nenfCombine (BinOp p (:&:) q) = nenf' p .&. nenf' q
      nenfCombine (BinOp p (:|:) q) = nenf' p .|. nenf' q
      nenfCombine (BinOp p (:=>:) q) = nenf' ((.~.) p) .|. nenf' q
      nenfCombine (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' q
      nenfNotCombine ((:~:) p) = p
      nenfNotCombine (BinOp p (:&:) q) = nenf' ((.~.) p) .|. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:|:) q) = nenf' ((.~.) p) .&. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:=>:) q) = nenf' p .&. nenf' ((.~.) q)
      nenfNotCombine (BinOp p (:<=>:) q) = nenf' p .<=>. nenf' ((.~.) q) -- really?  how is this asymmetrical?

nenf :: (IsPropositional formula atomic, Eq formula) => formula -> formula
nenf = nenf' . psimplify

{-
# Not (prime 2) ->
  <<~(~(((out_0 <=> x_0 /\ y_0) /\ ~out_1) /\ ~out_0 /\ out_1))>>

# nenf (Not (prime 2)) -> 
  <<((out_0 <=> x_0 /\ y_0) /\ ~out_1) /\ ~out_0 /\ out_1>>

> pretty ((.~.)(prime 2 :: Formula (Data.Logic.Harrison.PropExamples.Atom N)))
     (out0 ⇔ x0 ∧ y0) ∧ ¬out1 ∧ out1 ∧ ¬out0

> pretty (nenf ((.~.)(prime 2 :: Formula (Data.Logic.Harrison.PropExamples.Atom N))))
     (out0 ⇔ x0 ∨ y0) ∨ ¬out1 ∨ out1 ∨ ¬out0
-}

-- ------------------------------------------------------------------------- 
-- Disjunctive normal form (DNF) via truth tables.                           
-- ------------------------------------------------------------------------- 

list_conj :: (IsPropositional formula atomic, Ord formula) => Set.Set formula -> formula
list_conj l = maybe true (\ (x, xs) -> Set.fold (.&.) x xs) (Set.minView l)

list_disj :: IsPropositional formula atomic => Set.Set formula -> formula
list_disj l = maybe false (\ (x, xs) -> Set.fold (.|.) x xs) (Set.minView l)

mkLits :: (IsPropositional formula atomic, Ord formula, Ord atomic) =>
          Set.Set formula -> Map.Map atomic Bool -> formula
mkLits pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

allSatValuations :: Ord a => (Map.Map a Bool -> Bool) -> Map.Map a Bool -> Set.Set a -> [Map.Map a Bool]
allSatValuations subfn v pvs =
    case Set.minView pvs of
      Nothing -> if subfn v then [v] else []
      Just (p, ps) -> (allSatValuations subfn (Map.insert p False v) ps) ++
                      (allSatValuations subfn (Map.insert p True v) ps)

dnf0 :: forall formula atomic. (IsPropositional formula atomic, Ord atomic, Ord formula) => formula -> formula
dnf0 fm =
    list_disj (Set.fromList (map (mkLits (Set.map atomic pvs)) satvals))
    where
      satvals = allSatValuations (eval fm) Map.empty pvs
      pvs = atoms fm

-- ------------------------------------------------------------------------- 
-- DNF via distribution.                                                     
-- ------------------------------------------------------------------------- 

distrib :: IsPropositional formula atomic => formula -> formula
distrib fm =
    foldPropositional c tf a fm
    where
      c (BinOp p (:&:) s) =
          foldPropositional c' tf a s
          where c' (BinOp q (:|:) r) = distrib (p .&. q) .|. distrib (p .&. r)
                c' _ =
                    foldPropositional c'' tf a p
                    where c'' (BinOp q (:|:) r) = distrib (q .&. s) .|. distrib (r .&. s)
                          c'' _ = fm
      c _ = fm
      tf _ = fm
      a _ = fm

rawdnf :: IsPropositional formula atomic => formula -> formula
rawdnf fm =
    foldPropositional c tf a fm
    where
      c (BinOp p (:&:) q) = distrib (rawdnf p .&. rawdnf q)
      c (BinOp p (:|:) q) = rawdnf p .|. rawdnf q
      c _ = fm
      tf _ = fm
      a _ = fm

-- ------------------------------------------------------------------------- 
-- A version using a list representation.                                    
-- ------------------------------------------------------------------------- 

purednf :: (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => pf -> Set.Set (Set.Set lit)
purednf fm =
    foldPropositional c tf a fm
    where
      c (BinOp p (:&:) q) = Lib.distrib (purednf p) (purednf q)
      c (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      c ((:~:) p) = Set.map (Set.map (.~.)) (purednf p)
      c _ = error "purednf" -- Set.singleton (Set.singleton fm)
      tf x = Set.singleton (Set.singleton (fromBool x))
      a x = Set.singleton (Set.singleton (atomic x))

-- ------------------------------------------------------------------------- 
-- Filtering out trivial disjuncts (in this guise, contradictory).           
-- ------------------------------------------------------------------------- 

trivial :: (IsLiteral lit atom, Ord lit) => Set.Set lit -> Bool
trivial lits =
    not . Set.null $ Set.intersection neg (Set.map (.~.) pos)
    where (pos, neg) = Set.partition positive lits

-- ------------------------------------------------------------------------- 
-- With subsumption checking, done very naively (quadratic).                 
-- ------------------------------------------------------------------------- 

simpdnf :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => pf -> Set.Set (Set.Set lit)
simpdnf fm =
    foldPropositional c tf a fm
    where
      c :: Combination pf -> Set.Set (Set.Set lit)
      c _ = Set.filter (\ d -> not (setAny (\ d' -> Set.isProperSubsetOf d' d) djs)) djs
          where djs = Set.filter (not . trivial) (purednf (nnf fm))
      tf = bool Set.empty (Set.singleton Set.empty)
      a :: atom -> Set.Set (Set.Set lit)
      a x = Set.singleton (Set.singleton (atomic x))

-- ------------------------------------------------------------------------- 
-- Mapping back to a formula.                                                
-- ------------------------------------------------------------------------- 

dnf :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => Set.Set (Set.Set lit) -> pf
dnf = list_disj . Set.map (list_conj . Set.map (toPropositional id))

dnf' :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom) => pf -> pf
dnf' = dnf . (simpdnf :: pf -> Set.Set (Set.Set pf))

-- ------------------------------------------------------------------------- 
-- Conjunctive normal form (CNF) by essentially the same code.               
-- ------------------------------------------------------------------------- 

purecnf :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => pf -> Set.Set (Set.Set lit)
purecnf fm = Set.map (Set.map (.~.)) (purednf (nnf ((.~.) fm)))

simpcnf :: (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => pf -> Set.Set (Set.Set lit)
simpcnf fm =
    foldPropositional c tf a fm
    where
      tf = bool (Set.singleton Set.empty) Set.empty
      -- Discard any clause that is the proper subset of another clause
      c _ = Set.filter keep cjs
      keep x = not (setAny (`Set.isProperSubsetOf` x) cjs)
      cjs = Set.filter (not . trivial) (purecnf fm)
      a x = Set.singleton (Set.singleton (atomic x))

cnf :: forall pf lit atom. (IsPropositional pf atom, IsLiteral lit atom, Ord lit) => Set.Set (Set.Set lit) -> pf
cnf = list_conj . Set.map (list_disj . Set.map (toPropositional id))

cnf' :: forall pf atom. (IsPropositional pf atom, IsLiteral pf atom) => pf -> pf
cnf' = cnf . (simpcnf :: pf -> Set.Set (Set.Set pf))
#endif

