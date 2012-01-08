{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Harrison.FOL
    ( eval
    , list_disj
    , list_conj
    , var
    , fv
    , subst
    , generalize
    ) where

import Data.Logic.Classes.Apply (Apply(..), apply)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..), combine, binop)
import Data.Logic.Classes.Constants (Constants (fromBool, true, false))
import Data.Logic.Classes.Equals (AtomEq(foldAtomEq, equals), applyEq, pApp, (.=.))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), quant)
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(vt, foldTerm, fApp), fvt)
import Data.Logic.Classes.Variable (Variable(..))
import qualified Data.Logic.Classes.Term as C
import Data.Logic.Harrison.Formulas.FirstOrder (on_atoms)
import Data.Logic.Harrison.Lib ((|->), setAny)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Prelude hiding (pred)

-- =========================================================================
-- Basic stuff for first order logic.                                       
--                                                                          
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.) 
-- =========================================================================

-- ------------------------------------------------------------------------- 
-- Interpretation of formulas.                                               
-- ------------------------------------------------------------------------- 

eval :: FirstOrderFormula formula atom v => formula -> (atom -> Bool) -> Bool
eval fm v =
    foldFirstOrder qu co id at fm
    where
      qu _ _ p = eval p v
      co ((:~:) p) = not (eval p v)
      co (BinOp p (:&:) q) = eval p v && eval q v
      co (BinOp p (:|:) q) = eval p v || eval q v
      co (BinOp p (:=>:) q) = not (eval p v) || eval q v
      co (BinOp p (:<=>:) q) = eval p v == eval q v
      at = v

list_conj :: (Constants formula, Combinable formula) => Set.Set formula -> formula
list_conj l = maybe true (\ (x, xs) -> Set.fold (.&.) x xs) (Set.minView l)

list_disj :: (Constants formula, Combinable formula) => Set.Set formula -> formula
list_disj l = maybe false (\ (x, xs) -> Set.fold (.|.) x xs) (Set.minView l)

mkLits :: (FirstOrderFormula formula atom v, Ord formula) =>
          Set.Set formula -> (atom -> Bool) -> formula
mkLits pvs v = list_conj (Set.map (\ p -> if eval p v then p else (.~.) p) pvs)

-- -------------------------------------------------------------------------
-- Special case of applying a subfunction to the top *terms*.               
-- -------------------------------------------------------------------------

on_formula :: (FirstOrderFormula fol atom v, Apply atom p term) => (term -> term) -> fol -> fol
on_formula f = on_atoms (foldApply (\ p ts -> atomic (apply p (map f ts))) fromBool)

-- ------------------------------------------------------------------------- 
-- Parsing of terms.                                                         
-- ------------------------------------------------------------------------- 

{-
let is_const_name s = forall numeric (explode s) or s = "nil";;

let rec parse_atomic_term vs inp =
  match inp with
    [] -> failwith "term expected"
  | "("::rest -> parse_bracketed (parse_term vs) ")" rest
  | "-"::rest -> papply (fun t -> Fn("-",[t])) (parse_atomic_term vs rest)
  | f::"("::")"::rest -> Fn(f,[]),rest
  | f::"("::rest ->
      papply (fun args -> Fn(f,args))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | a::rest ->
      (if is_const_name a & not(mem a vs) then Fn(a,[]) else Var a),rest

and parse_term vs inp =
  parse_right_infix "::" (fun (e1,e2) -> Fn("::",[e1;e2]))
    (parse_right_infix "+" (fun (e1,e2) -> Fn("+",[e1;e2]))
       (parse_left_infix "-" (fun (e1,e2) -> Fn("-",[e1;e2]))
          (parse_right_infix "*" (fun (e1,e2) -> Fn("*",[e1;e2]))
             (parse_left_infix "/" (fun (e1,e2) -> Fn("/",[e1;e2]))
                (parse_left_infix "^" (fun (e1,e2) -> Fn("^",[e1;e2]))
                   (parse_atomic_term vs)))))) inp;;

let parset = make_parser (parse_term []);;

-- ------------------------------------------------------------------------- 
-- Parsing of formulas.                                                      
-- ------------------------------------------------------------------------- 

let parse_infix_atom vs inp =       
  let tm,rest = parse_term vs inp in
  if exists (nextin rest) ["="; "<"; "<="; ">"; ">="] then                     
        papply (fun tm' -> Atom(R(hd rest,[tm;tm'])))                          
               (parse_term vs (tl rest))                                       
  else failwith "";;
                                                               
let parse_atom vs inp =
  try parse_infix_atom vs inp with Failure _ ->                                
  match inp with                                                               
  | p::"("::")"::rest -> Atom(R(p,[])),rest                                    
  | p::"("::rest ->
      papply (fun args -> Atom(R(p,args)))
             (parse_bracketed (parse_list "," (parse_term vs)) ")" rest)
  | p::rest when p <> "(" -> Atom(R(p,[])),rest
  | _ -> failwith "parse_atom";;
                                                                               
let parse = make_parser                                                        
  (parse_formula (parse_infix_atom,parse_atom) []);;              

-- ------------------------------------------------------------------------- 
-- Set up parsing of quotations.                                             
-- ------------------------------------------------------------------------- 

let default_parser = parse;;

let secondary_parser = parset;;
-}

-- ------------------------------------------------------------------------- 
-- Printing of terms.                                                        
-- ------------------------------------------------------------------------- 
{-
let rec print_term prec fm =
  match fm with
    Var x -> print_string x
  | Fn("^",[tm1;tm2]) -> print_infix_term true prec 24 "^" tm1 tm2
  | Fn("/",[tm1;tm2]) -> print_infix_term true prec 22 " /" tm1 tm2
  | Fn("*",[tm1;tm2]) -> print_infix_term false prec 20 " *" tm1 tm2
  | Fn("-",[tm1;tm2]) -> print_infix_term true prec 18 " -" tm1 tm2
  | Fn("+",[tm1;tm2]) -> print_infix_term false prec 16 " +" tm1 tm2
  | Fn("::",[tm1;tm2]) -> print_infix_term false prec 14 "::" tm1 tm2
  | Fn(f,args) -> print_fargs f args

and print_fargs f args =
  print_string f;
  if args = [] then () else
   (print_string "(";
    open_box 0;
    print_term 0 (hd args); print_break 0 0;
    do_list (fun t -> print_string ","; print_break 0 0; print_term 0 t)
            (tl args);
    close_box();
    print_string ")")

and print_infix_term isleft oldprec newprec sym p q =
  if oldprec > newprec then (print_string "("; open_box 0) else ();
  print_term (if isleft then newprec else newprec+1) p;
  print_string sym;
  print_break (if String.sub sym 0 1 = " " then 1 else 0) 0;
  print_term (if isleft then newprec+1 else newprec) q;
  if oldprec > newprec then (close_box(); print_string ")") else ();;

let printert tm =
  open_box 0; print_string "<<|";
  open_box 0; print_term 0 tm; close_box();
  print_string "|>>"; close_box();;

#install_printer printert;;

-- ------------------------------------------------------------------------- 
-- Printing of formulas.                                                     
-- ------------------------------------------------------------------------- 

let print_atom prec (R(p,args)) =
  if mem p ["="; "<"; "<="; ">"; ">="] & length args = 2
  then print_infix_term false 12 12 (" "^p) (el 0 args) (el 1 args)
  else print_fargs p args;;

let print_fol_formula = print_qformula print_atom;;

#install_printer print_fol_formula;;

-- ------------------------------------------------------------------------- 
-- Examples in the main text.                                                
-- ------------------------------------------------------------------------- 

START_INTERACTIVE;;
<<forall x y. exists z. x < z /\ y < z>>;;

<<~(forall x. P(x)) <=> exists y. ~P(y)>>;;
END_INTERACTIVE;;
-}

-- ------------------------------------------------------------------------- 
-- Free variables in terms and formulas.                                     
-- ------------------------------------------------------------------------- 

-- | Return all variables occurring in a formula.
var :: forall formula atom v. FirstOrderFormula formula atom v => (atom -> Set.Set v) -> formula -> Set.Set v
var at fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ x p = Set.insert x (var at p)
      co ((:~:) p) = var at p
      co (BinOp p _ q) = Set.union (var at p) (var at q)
      tf _ = Set.empty

-- | Return the variables that occur free in a formula.
fv :: forall formula atom term v. (FirstOrderFormula formula atom v, Formula atom term v) => (atom -> Set.Set v) -> formula -> Set.Set v
fv at fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ x p = Set.delete x (fv at p)
      co ((:~:) p) = fv at p
      co (BinOp p _ q) = Set.union (fv at p) (fv at q)
      tf _ = Set.empty

-- ------------------------------------------------------------------------- 
-- Universal closure of a formula.                                           
-- ------------------------------------------------------------------------- 

generalize :: (FirstOrderFormula formula atom v, Formula atom term v) => (atom -> Set.Set v) -> formula -> formula
generalize at fm = Set.fold for_all fm (fv at fm)

-- ------------------------------------------------------------------------- 
-- Substitution in formulas, with variable renaming.                         
-- ------------------------------------------------------------------------- 

subst :: (FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
         (atom -> Set.Set v)
      -> (Map.Map v term -> atom -> atom)
      -> Map.Map v term -> formula -> formula
subst va sa env fm =
    foldFirstOrder qu co tf at fm
    where
      qu op x p = quant op x' (subst va sa ((x |-> vt x') env) p)
          where
            x' = if setAny (\ y -> Set.member x (fvt (fromMaybe (vt y) (Map.lookup y env)))) (Set.delete x (fv va p))
                 then variant x (fv va (subst va sa (Map.delete x env) p))
                 else x
      co ((:~:) p) = ((.~.) (subst va sa env p))
      co (BinOp p op q) = binop (subst va sa env p) op (subst va sa env q)
      tf = fromBool
      at = atomic . sa env

{-
-- |Replace each free occurrence of variable old with term new.
substitute :: forall formula atom term v f. (FirstOrderFormula formula atom v, Term term v f) => v -> term -> (atom -> formula) -> formula -> formula
substitute old new atom formula =
    foldTerm (\ new' -> if old == new' then formula else substitute' formula)
             (\ _ _ -> substitute' formula)
             new
    where
      substitute' =
          foldFirstOrder -- If the old variable appears in a quantifier
                -- we can stop doing the substitution.
                (\ q v f' -> quant q v (if old == v then f' else substitute' f'))
                (\ cm -> case cm of
                           ((:~:) f') -> combine ((:~:) (substitute' f'))
                           (BinOp f1 op f2) -> combine (BinOp (substitute' f1) op (substitute' f2)))
                fromBool
                atom
-}
{-
    substitute old new atom formula
    where 
      atom = foldAtomEq (\ p ts -> pApp p (map st ts)) fromBool (\ t1 t2 -> st t1 .=. st t2)
      st :: term -> term
      st t = foldTerm sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else vt v
-}

