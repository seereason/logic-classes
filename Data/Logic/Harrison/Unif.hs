{-# OPTIONS -Wall #-}
module Data.Logic.Harrison.Unif
    ( unify
    , solve
    , fullUnify
    , unifyAndApply
    ) where

import Data.Logic.Classes.Term (Term(..), tsubst)
import Data.Logic.Failing (Failing(..), failing)
import qualified Data.Map as Map
{-
(* ========================================================================= *)
(* Unification for first order terms.                                        *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec istriv env x t =
  match t with
    Var y -> y = x or defined env y & istriv env x (apply env y)
  | Fn(f,args) -> exists (istriv env x) args & failwith "cyclic";;
-}
isTrivial :: Term term v f => Map.Map v term -> v -> term -> Failing Bool
isTrivial env x t =
    foldTerm v f t
    where
      v y =
          if x == y
          then Success True
          else maybe (Success False) (isTrivial env x) (Map.lookup y env)
      f _ args =
          if any (failing (const False) id . isTrivial env x) args
          then Failure ["cyclic"]
          else Success False

{-
    foldT (\ y -> y == x || (defined env y && istriv env x (apply env y)))
          (\ _ args -> if any (istriv env x) args then error "cyclic" else False)
          t
-}
{-

(* ------------------------------------------------------------------------- *)
(* Main unification procedure                                                *)
(* ------------------------------------------------------------------------- *)

let rec unify env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fargs),Fn(g,gargs))::oth ->
        if f = g & length fargs = length gargs
        then unify env (zip fargs gargs @ oth)
        else failwith "impossible unification"
  | (Var x,t)::oth | (t,Var x)::oth ->
        if defined env x then unify env ((apply env x,t)::oth)
        else unify (if istriv env x t then env else (x|->t) env) oth;;
-}
unify :: Term term v f => Map.Map v term -> [(term,term)] -> Failing (Map.Map v term)
unify env [] = Success env
unify env ((a,b):oth) =
    foldTerm (vr b) (\ f fargs -> foldTerm (vr a) (fn f fargs) b) a
    where
      vr t x =
          maybe (isTrivial env x t >>= \ trivial -> unify (if trivial then env else Map.insert x t env) oth)
                (\ y -> unify env ((y, t) : oth))
                (Map.lookup x env)
      fn f fargs g gargs =
          if f == g && length fargs == length gargs
          then unify env (zip fargs gargs ++ oth)
          else Failure ["impossible unification"]

{-
(* ------------------------------------------------------------------------- *)
(* Solve to obtain a single instantiation.                                   *)
(* ------------------------------------------------------------------------- *)

let rec solve env =
  let env' = mapf (tsubst env) env in
  if env' = env then env else solve env';;
-}
solve :: Term term v f => Map.Map v term -> Map.Map v term
solve env =
    if env' == env then env else solve env'
    where env' = Map.map (tsubst env) env
{-

(* ------------------------------------------------------------------------- *)
(* Unification reaching a final solved form (often this isn't needed).       *)
(* ------------------------------------------------------------------------- *)

let fullunify eqs = solve (unify undefined eqs);;
-}
fullUnify :: Term term v f => [(term,term)] -> Failing (Map.Map v term)
fullUnify eqs = failing Failure (Success . solve) (unify Map.empty eqs)
{-

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let unify_and_apply eqs =
  let i = fullunify eqs in
  let apply (t1,t2) = tsubst i t1,tsubst i t2 in
  map apply eqs;;
-}
unifyAndApply :: Term term v f => [(term, term)] -> Failing [(term, term)]
unifyAndApply eqs =
    case fullUnify eqs of
      Failure x -> Failure x
      Success i -> Success (map (\ (t1, t2) -> (tsubst i t1, tsubst i t2)) eqs)
{-

START_INTERACTIVE;;
unify_and_apply [<<|f(x,g(y))|>>,<<|f(f(z),w)|>>];;

unify_and_apply [<<|f(x,y)|>>,<<|f(y,x)|>>];;

(****  unify_and_apply [<<|f(x,g(y))|>>,<<|f(y,x)|>>];; *****)

unify_and_apply [<<|x_0|>>,<<|f(x_1,x_1)|>>;
                 <<|x_1|>>,<<|f(x_2,x_2)|>>;
                 <<|x_2|>>,<<|f(x_3,x_3)|>>];;
END_INTERACTIVE;;
-}
