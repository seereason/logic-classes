{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
module Logic.Harrison.Skolem where

import Control.Monad.State (get, put)
import Logic.FirstOrder
import Logic.Harrison.Prop (nnf, psimplify1)
import Logic.Logic
import Logic.Monad (NormalT, LogicState(..))
import qualified Logic.Set as S

{-
(* ========================================================================= *)
(* Prenex and Skolem normal forms.                                           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Routine simplification. Like "psimplify" but with quantifier clauses.     *)
(* ------------------------------------------------------------------------- *)

let simplify1 fm =
  match fm with
    Forall(x,p) -> if mem x (fv p) then fm else p
  | Exists(x,p) -> if mem x (fv p) then fm else p
  | _ -> psimplify1 fm;;
-}
      
-- |Extend psimplify1 to handle quantifiers.  Any quantifier which has
-- no corresponding free occurrences of the quantified variable is
-- eliminated.
simplify1 :: FirstOrderLogic formula term v p f => formula -> formula
simplify1 fm =
    foldF (\ _ v p -> if S.member v (freeVars p) then fm else p)
          (\ _ -> psimplify1 fm)
          (\ _ -> psimplify1 fm)
          fm
{-

let rec simplify fm =
  match fm with
    Not p -> simplify1 (Not(simplify p))
  | And(p,q) -> simplify1 (And(simplify p,simplify q))
  | Or(p,q) -> simplify1 (Or(simplify p,simplify q))
  | Imp(p,q) -> simplify1 (Imp(simplify p,simplify q))
  | Iff(p,q) -> simplify1 (Iff(simplify p,simplify q))
  | Forall(x,p) -> simplify1(Forall(x,simplify p))
  | Exists(x,p) -> simplify1(Exists(x,simplify p))
  | _ -> fm;;
-}

-- |Do a bottom-up recursion to simplify a formula.
simplify :: FirstOrderLogic formula term v p f => formula -> formula
simplify fm =
    foldF (\ op v p -> simplify1 (quant op v (simplify p)))
          (\ cm -> case cm of
                     (:~:) p -> simplify1 ((.~.) (simplify p))
                     BinOp p op q -> simplify1 (combine (BinOp (simplify p) op (simplify q))))
          (\ _ -> simplify1 fm)
          fm
{-

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
simplify <<(forall x y. P(x) \/ (P(y) /\ false)) ==> exists z. Q>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec nnf fm =
  match fm with
    And(p,q) -> And(nnf p,nnf q)
  | Or(p,q) -> Or(nnf p,nnf q)
  | Imp(p,q) -> Or(nnf(Not p),nnf q)
  | Iff(p,q) -> Or(And(nnf p,nnf q),And(nnf(Not p),nnf(Not q)))
  | Not(Not p) -> nnf p
  | Not(And(p,q)) -> Or(nnf(Not p),nnf(Not q))
  | Not(Or(p,q)) -> And(nnf(Not p),nnf(Not q))
  | Not(Imp(p,q)) -> And(nnf p,nnf(Not q))
  | Not(Iff(p,q)) -> Or(And(nnf p,nnf(Not q)),And(nnf(Not p),nnf q))
  | Forall(x,p) -> Forall(x,nnf p)
  | Exists(x,p) -> Exists(x,nnf p)
  | Not(Forall(x,p)) -> Exists(x,nnf(Not p))
  | Not(Exists(x,p)) -> Forall(x,nnf(Not p))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Example of NNF function in action.                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
nnf <<(forall x. P(x))
      ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Prenex normal form.                                                       *)
(* ------------------------------------------------------------------------- *)

let rec pullquants fm =
  match fm with
    And(Forall(x,p),Forall(y,q)) ->
                          pullq(true,true) fm mk_forall mk_and x y p q
  | Or(Exists(x,p),Exists(y,q)) ->
                          pullq(true,true) fm mk_exists mk_or x y p q
  | And(Forall(x,p),q) -> pullq(true,false) fm mk_forall mk_and x x p q
  | And(p,Forall(y,q)) -> pullq(false,true) fm mk_forall mk_and y y p q
  | Or(Forall(x,p),q) ->  pullq(true,false) fm mk_forall mk_or x x p q
  | Or(p,Forall(y,q)) ->  pullq(false,true) fm mk_forall mk_or y y p q
  | And(Exists(x,p),q) -> pullq(true,false) fm mk_exists mk_and x x p q
  | And(p,Exists(y,q)) -> pullq(false,true) fm mk_exists mk_and y y p q
  | Or(Exists(x,p),q) ->  pullq(true,false) fm mk_exists mk_or x x p q
  | Or(p,Exists(y,q)) ->  pullq(false,true) fm mk_exists mk_or y y p q
  | _ -> fm

and pullq(l,r) fm quant op x y p q =
  let z = variant x (fv fm) in
  let p' = if l then subst (x |=> Var z) p else p
  and q' = if r then subst (y |=> Var z) q else q in
  quant z (pullquants(op p' q'));;

let rec prenex fm =
  match fm with
    Forall(x,p) -> Forall(x,prenex p)
  | Exists(x,p) -> Exists(x,prenex p)
  | And(p,q) -> pullquants(And(prenex p,prenex q))
  | Or(p,q) -> pullquants(Or(prenex p,prenex q))
  | _ -> fm;;

let pnf fm = prenex(nnf(simplify fm));;
-}

-- |Recursivly apply pullQuants anywhere a quantifier might not be
-- leftmost.
prenex :: (FirstOrderLogic formula term v p f) => formula -> formula 
prenex fm =
    foldF q c (\ _ -> fm) fm
    where
      q op x p = quant op x (prenex p)
      c (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      c (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      c _ = fm

-- |Perform transformations to move quantifiers outside of binary
-- operators:
-- 
-- @
--  Formula            Rewrites to
--  (1) ∀x F[x] & G        ∀x    (F[x] & G)
--  (2) ∀x F[x] & ∀x G[x]  ∀x ∀x (F[x] & G[x])
--  (3) ∃x F[x] & G        ∃x    (F[x] & G)
--  (4) ∃x F[x] & ∃x G[x]  ∃x Yz (F[x] & G[z]) -- rename
-- 
--  (5) ∀x F[x] | G        ∀x    (F[x] | G)
--  (6) ∀x F[x] | ∀x G[x]  ∀x ∀z (F[x] | G[z]) -- rename
--  (7) ∃x F[x] | G        ∃x    (F[x] | G)
--  (8) ∃x F[x] | ∃x G[x]  ∃x Yx (F[x] | G[x])
-- @
pullQuants :: forall formula term v p f. (FirstOrderLogic formula term v p f) => formula -> formula
pullQuants fm =
    foldF (\ _ _ _ -> fm) pullQuantsCombine (\ _ -> fm) fm
    where
      getQuant = foldF (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing)
      pullQuantsCombine ((:~:) _) = fm
      pullQuantsCombine (BinOp l op r) = 
          case (getQuant l, op, getQuant r) of
            (Just (All, vl, l'),    (:&:), Just (All, vr, r'))    -> pullq True  True  fm for_all (.&.) vl vr l' r'
            (Just (Exists, vl, l'), (:|:), Just (Exists, vr, r')) -> pullq True  True  fm exists  (.|.) vl vr l' r'
            (Just (All, vl, l'),    (:&:), _)                     -> pullq True  False fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just (All, vr, r'))    -> pullq False True  fm for_all (.&.) vr vr l  r'
            (Just (All, vl, l'),    (:|:), _)                     -> pullq True  False fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just (All, vr, r'))    -> pullq False True  fm for_all (.|.) vr vr l  r'
            (Just (Exists, vl, l'), (:&:), _)                     -> pullq True  False fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.&.) vr vr l  r'
            (Just (Exists, vl, l'), (:|:), _)                     -> pullq True  False fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: (FirstOrderLogic formula term v p f) =>
         Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> formula
pullq l r fm mkq op x y p q =
    let z = variant (freeVars fm) x
        p' = if l then substitute x (var z) p else p
        q' = if r then substitute y (var z) q else q
        fm' = pullQuants (op p' q') in
    mkq z fm'

-- |Find a variable name which is not in the variables set which is
-- stored in the monad.  This is initialized above with the free
-- variables in the formula.  (FIXME: this is not worth putting in
-- a monad, just pass in the set of free variables.)
variant :: (Enum v, Ord v) => S.Set v -> v -> v
variant names x = if S.member x names then variant names (succ x) else x
{-

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
pnf <<(forall x. P(x) \/ R(y))
      ==> exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Get the functions in a term and formula.                                  *)
(* ------------------------------------------------------------------------- *)

let rec funcs tm =
  match tm with
    Var x -> []
  | Fn(f,args) -> itlist (union ** funcs) args [f,length args];;

let functions fm =
  atom_union (fun (R(p,a)) -> itlist (union ** funcs) a []) fm;;

(* ------------------------------------------------------------------------- *)
(* Core Skolemization function.                                              *)
(* ------------------------------------------------------------------------- *)

let rec skolem fm fns =
  match fm with
    Exists(y,p) ->
        let xs = fv(fm) in
        let f = variant (if xs = [] then "c_"^y else "f_"^y) fns in
        let fx = Fn(f,map (fun x -> Var x) xs) in
        skolem (subst (y |=> fx) p) (f::fns)
  | Forall(x,p) -> let p',fns' = skolem p fns in Forall(x,p'),fns'
  | And(p,q) -> skolem2 (fun (p,q) -> And(p,q)) (p,q) fns
  | Or(p,q) -> skolem2 (fun (p,q) -> Or(p,q)) (p,q) fns
  | _ -> fm,fns

and skolem2 cons (p,q) fns =
  let p',fns' = skolem p fns in
  let q',fns'' = skolem q fns' in
  cons(p',q'),fns'';;

(* ------------------------------------------------------------------------- *)
(* Overall Skolemization function.                                           *)
(* ------------------------------------------------------------------------- *)

let askolemize fm =
  fst(skolem (nnf(simplify fm)) (map fst (functions fm)));;

let rec specialize fm =
  match fm with
    Forall(x,p) -> specialize p
  | _ -> fm;;

let skolemize fm = specialize(pnf(askolemize fm));;
-}

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
askolemize = skolem . nnf . simplify

-- |Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the NormalT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolem fm =
    foldF q c (\ _ -> return fm) fm
    where
      q Exists y p =
          do let xs = freeVars fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map var (S.toList xs))
             skolem (substitute y fx p)
      q All x p = skolem p >>= return . for_all x
      c (BinOp l (:&:) r) = skolem2 (.&.) l r
      c (BinOp l (:|:) r) = skolem2 (.|.) l r
      c _ = return fm

skolem2 :: (Monad m, FirstOrderLogic formula term v p f) =>
           (formula -> formula -> formula) -> formula -> formula -> NormalT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

specialize :: FirstOrderLogic formula term v p f => formula -> formula
specialize f =
    foldF q (\ _ -> f) (\ _ -> f) f
    where
      q All _ f' = specialize f'
      q _ _ _ = f
{-

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
skolemize <<exists y. x < y ==> forall u. exists v. x * u < y * v>>;;

skolemize
 <<forall x. P(x)
             ==> (exists y z. Q(y) \/ ~(exists z. P(z) /\ Q(z)))>>;;
END_INTERACTIVE;;
-}
