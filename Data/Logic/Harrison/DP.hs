{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Data.Logic.Harrison.DP
    ( dpll
    ) where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Negate (Negatable, (.~.), negated)
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.Logic.Harrison.DefCNF (Atom, defcnfs)
import Data.Logic.Harrison.Lib (allpairs, maximize', minimize', defined, setmapfilter, (|->))
import Data.Logic.Harrison.Prop (negative, positive, trivial, tautology)
import qualified Data.Map as Map
import qualified Data.Set.Extra as Set

-- ========================================================================= 
-- The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- The DP procedure.                                                         
-- ------------------------------------------------------------------------- 

one_literal_rule :: (PropositionalFormula pf a, Eq pf, Ord pf) => Set.Set (Set.Set pf) -> Failing (Set.Set (Set.Set pf))
one_literal_rule clauses =
    case Set.minView (Set.filter (\ cl -> Set.size cl == 1) clauses) of
      Nothing -> Failure ["one_literal_rule"]
      Just (s, _) ->
          let u = Set.findMin s in
          let u' = (.~.) u in
          let clauses1 = Set.filter (\ cl -> not (Set.member u cl)) clauses in
          Success (Set.map (\ cl -> Set.delete u' cl) clauses1)

affirmative_negative_rule :: (PropositionalFormula pf a, Eq pf, Ord pf) => Set.Set (Set.Set pf) -> Failing (Set.Set (Set.Set pf))
affirmative_negative_rule clauses =
  let (neg',pos) = Set.partition negative (Set.flatten clauses) in
  let neg = Set.map (.~.) neg' in
  let pos_only = Set.difference pos neg
      neg_only = Set.difference neg pos in
  let pure = Set.union pos_only (Set.map (.~.) neg_only) in
  if Set.null pure
  then Failure ["affirmative_negative_rule"]
  else Success (Set.filter (\ cl -> Set.null (Set.intersection cl pure)) clauses)

resolve_on :: forall pf atom. (PropositionalFormula pf atom, Ord pf) =>
              pf -> Set.Set (Set.Set pf) -> Set.Set (Set.Set pf)
resolve_on p clauses =
  let p' = (.~.) p
      (pos,notpos) = Set.partition (Set.member p) clauses in
  let (neg,other) = Set.partition (Set.member p') notpos in
  let pos' = Set.map (Set.filter (\ l -> l /= p)) pos
      neg' = Set.map (Set.filter (\ l -> l /= p')) neg in
  let res0 = allpairs Set.union pos' neg' in
  Set.union other (Set.filter (not . trivial) res0)

resolution_blowup :: forall formula. (Negatable formula, Ord formula) =>
                     Set.Set (Set.Set formula) -> formula -> Int
resolution_blowup cls l =
  let m = Set.size (Set.filter (Set.member l) cls)
      n = Set.size (Set.filter (Set.member ((.~.) l)) cls) in
  m * n - m - n

resolution_rule :: forall pf atomic. (PropositionalFormula pf atomic, Ord pf) =>
                   Set.Set (Set.Set pf) -> Failing (Set.Set (Set.Set pf))
resolution_rule clauses =
  let pvs = Set.filter positive (Set.flatten clauses) in
  case minimize' (resolution_blowup clauses) pvs of
    Just p -> Success (resolve_on p clauses)
    Nothing -> Failure ["resolution_rule"]

-- ------------------------------------------------------------------------- 
-- Overall procedure.                                                        
-- ------------------------------------------------------------------------- 

dp :: (PropositionalFormula pf atom, Eq pf, Ord pf) => Set.Set (Set.Set pf) -> Failing Bool
dp clauses =
  if Set.null clauses
  then Success True
  else if Set.member Set.empty clauses
       then Success False
       else case one_literal_rule clauses >>= dp of
              Success x -> Success x
              Failure _ ->
                  case affirmative_negative_rule clauses >>= dp of
                    Success x -> Success x
                    Failure _ -> resolution_rule clauses >>= dp

-- ------------------------------------------------------------------------- 
-- Davis-Putnam satisfiability tester and tautology checker.                 
-- ------------------------------------------------------------------------- 

dpsat :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
         pf -> Failing Bool
dpsat fm = dp (defcnfs fm)

dptaut :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
          pf -> Failing Bool
dptaut fm = dpsat((.~.) fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

{-
test01 =
    TestCase (assertEqual "tautology(prime 11)" 

START_INTERACTIVE
tautology(prime 11)

dptaut(prime 11)
END_INTERACTIVE
-}

-- ------------------------------------------------------------------------- 
-- The same thing but with the DPLL procedure.                               
-- ------------------------------------------------------------------------- 

posneg_count :: forall formula. (Negatable formula, Ord formula) =>
                Set.Set (Set.Set formula) -> formula -> Int
posneg_count cls l =                         
  let m = Set.size(Set.filter (Set.member l) cls)                 
      n = Set.size(Set.filter (Set.member ((.~.) l)) cls) in
  m + n                                  

dpll :: forall atomic pf. (PropositionalFormula pf atomic, Ord pf) =>
        Set.Set (Set.Set pf) -> Failing Bool
dpll clauses =       
  if clauses == Set.empty
  then Success True
  else if Set.member Set.empty clauses
       then Success False
       else case one_literal_rule clauses >>= dpll of
              Success x -> Success x
              Failure _ ->
                  case affirmative_negative_rule clauses >>= dpll of
                    Success x -> Success x
                    Failure _ ->
                        let pvs = Set.filter positive (Set.flatten clauses) in
                        case maximize' (posneg_count clauses) pvs of
                          Nothing -> Failure ["dpll"]
                          Just p -> 
                              case (dpll (Set.insert (Set.singleton p) clauses), dpll (Set.insert (Set.singleton ((.~.) p)) clauses)) of
                                (Success a, Success b) -> Success (a || b)
                                (Failure a, Failure b) -> Failure (a ++ b)
                                (Failure a, _) -> Failure a
                                (_, Failure b) -> Failure b

dpllsat :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
           pf -> Failing Bool
dpllsat fm = dpll(defcnfs fm)

dplltaut :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
            pf -> Failing Bool
dplltaut fm = dpllsat ((.~.) fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

{-
START_INTERACTIVE
dplltaut(prime 11)
END_INTERACTIVE
-}

-- ------------------------------------------------------------------------- 
-- Iterative implementation with explicit trail instead of recursion.        
-- ------------------------------------------------------------------------- 

data TrailMix = Guessed | Deduced deriving (Eq, Ord)

unassigned :: forall formula. (Negatable formula, Ord formula) =>
              Set.Set (Set.Set formula) -> Set.Set (formula, TrailMix) -> Set.Set formula
unassigned cls trail =
    Set.difference (Set.flatten (Set.map (Set.map litabs) cls)) (Set.map (litabs . fst) trail)
    where litabs p = if negated p then (.~.) p else p

unit_subpropagate :: forall formula. (Negatable formula, Ord formula) =>
                     (Set.Set (Set.Set formula), Map.Map formula (), Set.Set (formula, TrailMix))
                  -> (Set.Set (Set.Set formula), Map.Map formula (), Set.Set (formula, TrailMix))
unit_subpropagate (cls,fn,trail) =
  let cls' = Set.map (Set.filter (not . defined fn . (.~.))) cls in
  let uu cs =
          case Set.minView cs of
            Just (c, _) -> if Set.size cs == 1 && not (defined fn c)
                           then Success cs
                           else Failure ["unit_subpropagate"] in
  let newunits = Set.flatten (setmapfilter uu cls') in
  if Set.null newunits then (cls',fn,trail) else
  let trail' = Set.fold (\ p t -> Set.insert (p,Deduced) t) trail newunits
      fn' = Set.fold (\ u -> (u |-> ())) fn newunits in
  unit_subpropagate (cls',fn',trail')

unit_propagate :: forall t. (Negatable t, Ord t) =>
                  (Set.Set (Set.Set t), Set.Set (t, TrailMix))
               -> (Set.Set (Set.Set t), Set.Set (t, TrailMix))
unit_propagate (cls,trail) =
  let fn = Set.fold (\ (x,_) -> (x |-> ())) Map.empty trail in
  let (cls',fn',trail') = unit_subpropagate (cls,fn,trail) in (cls',trail')

backtrack :: forall t. Set.Set (t, TrailMix) -> Set.Set (t, TrailMix)
backtrack trail =
  case Set.minView trail of
    Just ((p,Deduced), tt) -> backtrack tt
    _ -> trail

dpli :: forall atomic pf. (PropositionalFormula pf atomic, Ord pf) =>
        Set.Set (Set.Set pf) -> Set.Set (pf, TrailMix) -> Failing Bool
dpli cls trail =
  let (cls', trail') = unit_propagate (cls, trail) in
  if Set.member Set.empty cls' then
    case Set.minView trail of
      Just ((p,Guessed), tt) -> dpli cls (Set.insert ((.~.) p, Deduced) tt)
      _ -> Success False
  else
      case unassigned cls (trail' :: Set.Set (pf, TrailMix)) of
        s | Set.null s -> Success True
        ps -> case maximize' (posneg_count cls') ps of
                Just p -> dpli cls (Set.insert (p :: pf, Guessed) trail')
                Nothing -> Failure ["dpli"]

dplisat :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
           pf -> Failing Bool
dplisat fm = dpli (defcnfs fm) Set.empty

dplitaut :: forall pf. (PropositionalFormula pf Atom, Ord pf) =>
            pf -> Failing Bool
dplitaut fm = dplisat((.~.) fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- With simple non-chronological backjumping and learning.                   
-- ------------------------------------------------------------------------- 

backjump :: forall a. (Negatable a, Ord a) =>
            Set.Set (Set.Set a) -> a -> Set.Set (a, TrailMix) -> Set.Set (a, TrailMix)
backjump cls p trail =
  case Set.minView (backtrack trail) of
    Just ((q,Guessed), tt) ->
        let (cls',trail') = unit_propagate (cls, Set.insert (p,Guessed) tt) in
        if Set.member Set.empty cls' then backjump cls p tt else trail
    _ -> trail

dplb :: forall a. (Negatable a, Ord a) =>
        Set.Set (Set.Set a) -> Set.Set (a, TrailMix) -> Failing Bool
dplb cls trail =
  let (cls',trail') = unit_propagate (cls,trail) in
  if Set.member Set.empty cls' then
    case Set.minView (backtrack trail) of
      Just ((p,Guessed), tt) ->
        let gretrail' = backjump cls p tt in
        let declits = Set.filter (\ (_,d) -> d == Guessed) trail' in
        let conflict = Set.insert ((.~.) p) (Set.map ((.~.) . fst) declits) in
        dplb (Set.insert conflict cls) (Set.insert ((.~.) p,Deduced) trail')
      _ -> Success False
  else
    case unassigned cls trail' of
      s | Set.null s -> Success True
      ps -> case maximize' (posneg_count cls') ps of
              Just p -> dplb cls (Set.insert (p,Guessed) trail')
              Nothing -> Failure ["dpib"]
            
dplbsat :: forall a. (PropositionalFormula a Atom, Ord a) =>
           a -> Failing Bool
dplbsat fm = dplb (defcnfs fm) Set.empty

dplbtaut :: forall a. (PropositionalFormula a Atom, Ord a) =>
            a -> Failing Bool
dplbtaut fm = dplbsat((.~.) fm) >>= return . not

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 
{-
START_INTERACTIVE
dplitaut(prime 101)
dplbtaut(prime 101)
END_INTERACTIVE
-}
