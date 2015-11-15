{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Harrison.Formulas.FirstOrder
    ( antecedent
    , consequent
    , on_atoms
    , over_atoms
    , atom_union
    ) where

import Data.Logic.ATP.Formulas (IsFormula(AtomOf))
import Data.Logic.ATP.Lit ((.~.))
import Data.Logic.ATP.Prop (BinOp(..), binop)
import Data.Logic.ATP.Quantified (IsQuantified(..), quant)
import qualified Data.Set as Set

-- ------------------------------------------------------------------------- 
-- General parsing of iterated infixes.                                      
-- ------------------------------------------------------------------------- 

{-
let rec parse_ginfix opsym opupdate sof subparser inp =
  let e1,inp1 = subparser inp in
  if inp1 <> [] & hd inp1 = opsym then
     parse_ginfix opsym opupdate (opupdate sof e1) subparser (tl inp1)
  else sof e1,inp1;;

let parse_left_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> opcon(f e1,e2)) (fun x -> x);;

let parse_right_infix opsym opcon =
  parse_ginfix opsym (fun f e1 e2 -> f(opcon(e1,e2))) (fun x -> x);;

let parse_list opsym =
  parse_ginfix opsym (fun f e1 e2 -> (f e1)@[e2]) (fun x -> [x]);;

-- ------------------------------------------------------------------------- 
-- Other general parsing combinators.                                        
-- ------------------------------------------------------------------------- 

let papply f (ast,rest) = (f ast,rest);;

let nextin inp tok = inp <> [] & hd inp = tok;;

let parse_bracketed subparser cbra inp =
  let ast,rest = subparser inp in
  if nextin rest cbra then ast,tl rest
  else failwith "Closing bracket expected";;

-- ------------------------------------------------------------------------- 
-- Parsing of formulas, parametrized by atom parser "pfn".                   
-- ------------------------------------------------------------------------- 

let rec parse_atomic_formula (ifn,afn) vs inp =
  match inp with
    [] -> failwith "formula expected"
  | "false"::rest -> False,rest
  | "true"::rest -> True,rest
  | "("::rest -> (try ifn vs inp with Failure _ ->
                  parse_bracketed (parse_formula (ifn,afn) vs) ")" rest)
  | "~"::rest -> papply (fun p -> Not p)
                        (parse_atomic_formula (ifn,afn) vs rest)
  | "forall"::x::rest ->
        parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Forall(x,p)) x rest
  | "exists"::x::rest ->
        parse_quant (ifn,afn) (x::vs) (fun (x,p) -> Exists(x,p)) x rest
  | _ -> afn vs inp

and parse_quant (ifn,afn) vs qcon x inp =
   match inp with
     [] -> failwith "Body of quantified term expected"
   | y::rest ->
        papply (fun fm -> qcon(x,fm))
               (if y = "." then parse_formula (ifn,afn) vs rest
                else parse_quant (ifn,afn) (y::vs) qcon y rest)

and parse_formula (ifn,afn) vs inp =
   parse_right_infix "<=>" (fun (p,q) -> Iff(p,q))
     (parse_right_infix "==>" (fun (p,q) -> Imp(p,q))
         (parse_right_infix "\\/" (fun (p,q) -> Or(p,q))
             (parse_right_infix "/\\" (fun (p,q) -> And(p,q))
                  (parse_atomic_formula (ifn,afn) vs)))) inp;;

-- ------------------------------------------------------------------------- 
-- Printing of formulas, parametrized by atom printer.                       
-- ------------------------------------------------------------------------- 

let bracket p n f x y =
  (if p then print_string "(" else ());
  open_box n; f x y; close_box();
  (if p then print_string ")" else ());;

let rec strip_quant fm =
  match fm with
    Forall(x,(Forall(y,p) as yp)) | Exists(x,(Exists(y,p) as yp)) ->
        let xs,q = strip_quant yp in x::xs,q
  |  Forall(x,p) | Exists(x,p) -> [x],p
  | _ -> [],fm;;

let print_formula pfn =
  let rec print_formula pr fm =
    match fm with
      False -> print_string "false"
    | True -> print_string "true"
    | Atom(pargs) -> pfn pr pargs
    | Not(p) -> bracket (pr > 10) 1 (print_prefix 10) "~" p
    | And(p,q) -> bracket (pr > 8) 0 (print_infix 8 "/\\") p q
    | Or(p,q) ->  bracket (pr > 6) 0 (print_infix  6 "\\/") p q
    | Imp(p,q) ->  bracket (pr > 4) 0 (print_infix 4 "==>") p q
    | Iff(p,q) ->  bracket (pr > 2) 0 (print_infix 2 "<=>") p q
    | Forall(x,p) -> bracket (pr > 0) 2 print_qnt "forall" (strip_quant fm)
    | Exists(x,p) -> bracket (pr > 0) 2 print_qnt "exists" (strip_quant fm)
  and print_qnt qname (bvs,bod) =
    print_string qname;
    do_list (fun v -> print_string " "; print_string v) bvs;
    print_string "."; print_space(); open_box 0;
    print_formula 0 bod;
    close_box()
  and print_prefix newpr sym p =
   print_string sym; print_formula (newpr+1) p
  and print_infix newpr sym p q =
    print_formula (newpr+1) p;
    print_string(" "^sym); print_space();
    print_formula newpr q in
  print_formula 0;;

let print_qformula pfn fm =
  open_box 0; print_string "<<";
  open_box 0; print_formula pfn fm; close_box();
  print_string ">>"; close_box();;

-- ------------------------------------------------------------------------- 
-- OCaml won't let us use the constructors.                                  
-- ------------------------------------------------------------------------- 

let mk_and p q = And(p,q) and mk_or p q = Or(p,q)
and mk_imp p q = Imp(p,q) and mk_iff p q = Iff(p,q)
and mk_forall x p = Forall(x,p) and mk_exists x p = Exists(x,p);;

-- ------------------------------------------------------------------------- 
-- Destructors.                                                              
-- ------------------------------------------------------------------------- 

let dest_iff fm =
  match fm with Iff(p,q) -> (p,q) | _ -> failwith "dest_iff";;

let dest_and fm =
  match fm with And(p,q) -> (p,q) | _ -> failwith "dest_and";;

let rec conjuncts fm =
  match fm with And(p,q) -> conjuncts p @ conjuncts q | _ -> [fm];;

let dest_or fm =
  match fm with Or(p,q) -> (p,q) | _ -> failwith "dest_or";;

let rec disjuncts fm =
  match fm with Or(p,q) -> disjuncts p @ disjuncts q | _ -> [fm];;

let dest_imp fm =
  match fm with Imp(p,q) -> (p,q) | _ -> failwith "dest_imp";;
-}

antecedent :: IsQuantified formula => formula -> formula
antecedent formula =
    foldQuantified (\ _ _ _ -> err) c (\ _ -> err) (\ _ -> err) (\ _ -> err) formula
    where
      c p (:=>:) _ = p
      c _ _ _ = err
      err = error "antecedent"

consequent :: IsQuantified formula => formula -> formula
consequent formula =
    foldQuantified (\ _ _ _ -> err) c (\ _ -> err) (\ _ -> err) (\ _ -> err) formula
    where
      c _ (:=>:) q = q
      c _ _ _ = err
      err = error "consequent"

-- ------------------------------------------------------------------------- 
-- Apply a function to the atoms, otherwise keeping structure.               
-- ------------------------------------------------------------------------- 

on_atoms :: forall formula. IsQuantified formula => (AtomOf formula -> formula) -> formula -> formula
on_atoms f fm =
    foldQuantified qu co ne tf at fm
    where
      qu op v fm' = quant op v (on_atoms f fm')
      ne fm' = (.~.) (on_atoms f fm')
      co f1 op f2 = binop (on_atoms f f1) op (on_atoms f f2)
      tf _ = fm
      at = f

-- ------------------------------------------------------------------------- 
-- Formula analog of list iterator "itlist".                                 
-- ------------------------------------------------------------------------- 

over_atoms :: IsQuantified formula => (AtomOf formula -> b -> b) -> formula -> b -> b
over_atoms f fm b =
    foldQuantified qu co ne tf pr fm
    where
      qu _ _ p = over_atoms f p b
      ne p = over_atoms f p b
      co p _ q = over_atoms f p (over_atoms f q b)
      tf _ = b
      pr atom = f atom b

-- ------------------------------------------------------------------------- 
-- Special case of a union of the results of a function over the atoms.      
-- ------------------------------------------------------------------------- 

atom_union :: (IsQuantified formula, Ord b) => (AtomOf formula -> Set.Set b) -> formula -> Set.Set b
atom_union f fm = over_atoms (\ h t -> Set.union (f h) t) fm Set.empty
