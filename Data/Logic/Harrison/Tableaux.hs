{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Harrison.Tableaux
    ( unify_literals
    , unifyAtomsEq
    , deepen
    ) where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Equals (AtomEq, zipAtomsEq)
import Data.Logic.Classes.Literal (Literal, zipLiterals)
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Harrison.Unif (unify)
import qualified Data.Map as Map
import Debug.Trace (trace)

-- =========================================================================
-- Tableaux, seen as an optimized version of a Prawitz-like procedure.       
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- Unify literals (just pretend the toplevel relation is a function).        
-- ------------------------------------------------------------------------- 

{-
unify_literals :: forall lit term atom v p f. (Literal lit atom v, AtomEq atom p term, Term term v f) =>
                 Map.Map v term -> lit -> lit -> Failing (Map.Map v term)
-}
unify_literals :: forall lit atom term v f. (Literal lit atom v, Term term v f) =>
                  (Map.Map v term -> atom -> atom -> Failing (Map.Map v term))
               -> Map.Map v term -> lit -> lit -> Failing (Map.Map v term)
unify_literals ua env f1 f2 =
    maybe err id (zipLiterals co tf at f1 f2)
    where
      -- co :: lit -> lit -> Maybe (Failing (Map.Map v term))
      co p q = Just $ unify_literals ua env p q
      tf p q = if p == q then Just $ unify env [] else Nothing
      -- at :: atom -> atom -> Maybe (Failing (Map.Map v term))
      at a1 a2 = Just $ ua env a1 a2
      err = Failure ["Can't unify literals"]

unifyAtomsEq :: forall v f atom p term.
                (AtomEq atom p term, Term term v f) =>
                Map.Map v term -> atom -> atom -> Failing (Map.Map v term)
unifyAtomsEq env a1 a2 =
    maybe err id (zipAtomsEq ap tf eq a1 a2)
    where
      ap p1 ts1 p2 ts2 =
          if p1 == p2 && length ts1 == length ts2
          then Just $ unify env (zip ts1 ts2)
          else Nothing
      tf p q = if p == q then Just $ unify env [] else Nothing
      eq pl pr ql qr = Just $ unify env [(pl, ql), (pr, qr)]
      err = Failure ["Can't unify atoms"]

-- ------------------------------------------------------------------------- 
-- Unify complementary literals.                                             
-- ------------------------------------------------------------------------- 
{-
unify_complements env (p,q) = unify_literals env (p,negate q)

-- ------------------------------------------------------------------------- 
-- Unify and refute a set of disjuncts.                                      
-- ------------------------------------------------------------------------- 

unify_refute djs env =
  case djs of
    [] -> env
    d : odjs -> let (pos,neg) = partition positive d in
               tryfind (unify_refute odjs . unify_complements env)
                       (allpairs (\ p q -> (p,q)) pos neg);;

-- ------------------------------------------------------------------------- 
-- Hence a Prawitz-like procedure (using unification on DNF).                
-- ------------------------------------------------------------------------- 

prawitz_loop djs0 fvs djs n =
    let l = length fvs in
    let newvars = map (\ k -> "_" ++ show (n * l + k)) [1..l] in
    let inst = fpf fvs (map Var newvars) in
    let djs1 = distrib (image (image (subst inst)) djs0) djs in
    case (unify_refute djs1 undefined,(n + 1)) of
      Left _ -> prawitz_loop djs0 fvs djs1 (n + 1)
      Right x -> x

prawitz fm =
  let fm0 = skolemize(Not(generalize fm)) in
  snd(prawitz_loop (simpdnf fm0) (fv fm0) [[]] 0);;

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test01 = TestCase $ assertEqual "p20 - prawitz" expected input
    where input = prawitz fm
          fm = (for_all "x" (for_all "y" (exists "z" (for_all "w" (pApp "P" [var "x"] .&. pApp "Q" [var "y"] .=>.
                                                                   pApp "R" [var "z"] .&. pApp "U" [var "w"]))))) .=>.
               (exists "x" (exists "y" (pApp "P" [var "x"] .&. pApp "Q" [var "y"]))) .=>. (exists "z" (pApp "R" [var "z"]))
          expected = false

-- ------------------------------------------------------------------------- 
-- Comparison of number of ground instances.                                 
-- ------------------------------------------------------------------------- 

compare fm =
    (prawitz fm, davisputnam fm)
{-
START_INTERACTIVE;;
test02 = TestCase $ assertEqual "p19" expected input
    where input = compare (exists "x" (forall "y" (for_all "z" ((pApp "P" [var "y"] .=>. pApp "Q" [var "z"]) .=>. pApp "P" [var "x"] .=>. pApp "Q" [var "x"]))))

let p20 = compare
 <<(forall x y. exists z. forall w. P[var "x"] .&. Q[var "y"] .=>. R[var "z"] .&. U[var "w"])
   .=>. (exists x y. P[var "x"] .&. Q[var "y"]) .=>. (exists z. R[var "z"])>>;;

let p24 = compare
 <<~(exists x. U[var "x"] .&. Q[var "x"]) .&.
   (forall x. P[var "x"] .=>. Q[var "x"] .|. R[var "x"]) .&.
   ~(exists x. P[var "x"] .=>. (exists x. Q[var "x"])) .&.
   (forall x. Q[var "x"] .&. R[var "x"] .=>. U[var "x"])
   .=>. (exists x. P[var "x"] .&. R[var "x"])>>;;

let p39 = compare
 <<~(exists x. forall y. P(y,x) .<=>. ~P(y,y))>>;;

let p42 = compare
 <<~(exists y. forall x. P(x,y) .<=>. ~(exists z. P(x,z) .&. P(z,x)))>>;;

{- **** Too slow?

let p43 = compare
 <<(forall x y. Q(x,y) .<=>. forall z. P(z,x) .<=>. P(z,y))
   .=>. forall x y. Q(x,y) .<=>. Q(y,x)>>;;

 ***** -}

let p44 = compare
 <<(forall x. P[var "x"] .=>. (exists y. G[var "y"] .&. H(x,y)) .&.
   (exists y. G[var "y"] .&. ~H(x,y))) .&.
   (exists x. J[var "x"] .&. (forall y. G[var "y"] .=>. H(x,y)))
   .=>. (exists x. J[var "x"] .&. ~P[var "x"])>>;;

let p59 = compare
 <<(forall x. P[var "x"] .<=>. ~P(f[var "x"])) .=>. (exists x. P[var "x"] .&. ~P(f[var "x"]))>>;;

let p60 = compare
 <<forall x. P(x,f[var "x"]) .<=>.
             exists y. (forall z. P(z,y) .=>. P(z,f[var "x"])) .&. P(x,y)>>;;

END_INTERACTIVE;;

-- ------------------------------------------------------------------------- 
-- More standard tableau procedure, effectively doing DNF incrementally.     
-- ------------------------------------------------------------------------- 

let rec tableau (fms,lits,n) cont (env,k) =
  if n < 0 then error "no proof at this level" else
  match fms with
    [] -> error "tableau: no proof"
  | And(p,q) : unexp ->
      tableau (p : q : unexp,lits,n) cont (env,k)
  | Or(p,q) : unexp ->
      tableau (p : unexp,lits,n) (tableau (q : unexp,lits,n) cont) (env,k)
  | Forall(x,p) : unexp ->
      let y = Var("_" ++ string_of_int k) in
      let p' = subst (x |=> y) p in
      tableau (p' : unexp@[Forall(x,p)],lits,n-1) cont (env,k+1)
  | fm : unexp ->
      try tryfind (\ l -> cont(unify_complements env (fm,l),k)) lits
      with Failure _ -> tableau (unexp,fm : lits,n) cont (env,k);;
-}
-}

-- | Try f with higher and higher values of n until it succeeds, or
-- optional maximum depth limit is exceeded.
deepen :: (Int -> Failing t) -> Int -> Maybe Int -> Failing (t, Int)
deepen _ n (Just m) | n > m = Failure ["Exceeded maximum depth limit"]
deepen f n m =
    -- If no maximum depth limit is given print a trace of the
    -- levels tried.  The assumption is that we are running
    -- interactively.
    let n' = maybe (trace ("Searching with depth limit " ++ show n) n) (const n) m in
    case f n' of
      Failure _ -> deepen f (n + 1) m
      Success x -> Success (x, n)

{-
let tabrefute fms =
  deepen (\ n -> tableau (fms,[],n) (\ x -> x) (undefined,0); n) 0;;

let tab fm =
  let sfm = askolemize(Not(generalize fm)) in
  if sfm = False then 0 else tabrefute [sfm];;

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

START_INTERACTIVE;;
let p38 = tab
 <<(forall x.
     P[var "a"] .&. (P[var "x"] .=>. (exists y. P[var "y"] .&. R(x,y))) .=>.
     (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))) .<=>.
   (forall x.
     (~P[var "a"] .|. P[var "x"] .|. (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))) .&.
     (~P[var "a"] .|. ~(exists y. P[var "y"] .&. R(x,y)) .|.
     (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))))>>;;
END_INTERACTIVE;;

-- ------------------------------------------------------------------------- 
-- Try to split up the initial formula first; often a big improvement.       
-- ------------------------------------------------------------------------- 

let splittab fm = 
  map tabrefute (simpdnf(askolemize(Not(generalize fm))));;

-- ------------------------------------------------------------------------- 
-- Example: the Andrews challenge.                                           
-- ------------------------------------------------------------------------- 

START_INTERACTIVE;;
let p34 = splittab
 <<((exists x. forall y. P[var "x"] .<=>. P[var "y"]) .<=>.
    ((exists x. Q[var "x"]) .<=>. (forall y. Q[var "y"]))) .<=>.
   ((exists x. forall y. Q[var "x"] .<=>. Q[var "y"]) .<=>.
    ((exists x. P[var "x"]) .<=>. (forall y. P[var "y"])))>>;;

-- ------------------------------------------------------------------------- 
-- Another nice example from EWD 1602.                                       
-- ------------------------------------------------------------------------- 

let ewd1062 = splittab
 <<(forall x. x <= x) .&.
   (forall x y z. x <= y .&. y <= z .=>. x <= z) .&.
   (forall x y. f[var "x"] <= y .<=>. x <= g[var "y"])
   .=>. (forall x y. x <= y .=>. f[var "x"] <= f[var "y"]) .&.
       (forall x y. x <= y .=>. g[var "x"] <= g[var "y"])>>;;
END_INTERACTIVE;;

-- ------------------------------------------------------------------------- 
-- Do all the equality-free Pelletier problems, and more, as examples.       
-- ------------------------------------------------------------------------- 

{- **********

let p1 = time splittab
 <<p .=>. q .<=>. ~q .=>. ~p>>;;

let p2 = time splittab
 <<~ ~p .<=>. p>>;;

let p3 = time splittab
 <<~(p .=>. q) .=>. q .=>. p>>;;

let p4 = time splittab
 <<~p .=>. q .<=>. ~q .=>. p>>;;

let p5 = time splittab
 <<(p .|. q .=>. p .|. r) .=>. p .|. (q .=>. r)>>;;

let p6 = time splittab
 <<p .|. ~p>>;;

let p7 = time splittab
 <<p .|. ~ ~ ~p>>;;

let p8 = time splittab
 <<((p .=>. q) .=>. p) .=>. p>>;;

let p9 = time splittab
 <<(p .|. q) .&. (~p .|. q) .&. (p .|. ~q) .=>. ~(~q .|. ~q)>>;;

let p10 = time splittab
 <<(q .=>. r) .&. (r .=>. p .&. q) .&. (p .=>. q .&. r) .=>. (p .<=>. q)>>;;

let p11 = time splittab
 <<p .<=>. p>>;;

let p12 = time splittab
 <<((p .<=>. q) .<=>. r) .<=>. (p .<=>. (q .<=>. r))>>;;

let p13 = time splittab
 <<p .|. q .&. r .<=>. (p .|. q) .&. (p .|. r)>>;;

let p14 = time splittab
 <<(p .<=>. q) .<=>. (q .|. ~p) .&. (~q .|. p)>>;;

let p15 = time splittab
 <<p .=>. q .<=>. ~p .|. q>>;;

let p16 = time splittab
 <<(p .=>. q) .|. (q .=>. p)>>;;

let p17 = time splittab
 <<p .&. (q .=>. r) .=>. s .<=>. (~p .|. q .|. s) .&. (~p .|. ~r .|. s)>>;;

-- ------------------------------------------------------------------------- 
-- Pelletier problems: monadic predicate logic.                              
-- ------------------------------------------------------------------------- 

let p18 = time splittab
 <<exists y. forall x. P[var "y"] .=>. P[var "x"]>>;;

let p19 = time splittab
 <<exists x. forall y z. (P[var "y"] .=>. Q[var "z"]) .=>. P[var "x"] .=>. Q[var "x"]>>;;

let p20 = time splittab
 <<(forall x y. exists z. forall w. P[var "x"] .&. Q[var "y"] .=>. R[var "z"] .&. U[var "w"])
   .=>. (exists x y. P[var "x"] .&. Q[var "y"]) .=>. (exists z. R[var "z"])>>;;

let p21 = time splittab
 <<(exists x. P .=>. Q[var "x"]) .&. (exists x. Q[var "x"] .=>. P)
   .=>. (exists x. P .<=>. Q[var "x"])>>;;

let p22 = time splittab
 <<(forall x. P .<=>. Q[var "x"]) .=>. (P .<=>. (forall x. Q[var "x"]))>>;;

let p23 = time splittab
 <<(forall x. P .|. Q[var "x"]) .<=>. P .|. (forall x. Q[var "x"])>>;;

let p24 = time splittab
 <<~(exists x. U[var "x"] .&. Q[var "x"]) .&.
   (forall x. P[var "x"] .=>. Q[var "x"] .|. R[var "x"]) .&.
   ~(exists x. P[var "x"] .=>. (exists x. Q[var "x"])) .&.
   (forall x. Q[var "x"] .&. R[var "x"] .=>. U[var "x"]) .=>.
   (exists x. P[var "x"] .&. R[var "x"])>>;;

let p25 = time splittab
 <<(exists x. P[var "x"]) .&.
   (forall x. U[var "x"] .=>. ~G[var "x"] .&. R[var "x"]) .&.
   (forall x. P[var "x"] .=>. G[var "x"] .&. U[var "x"]) .&.
   ((forall x. P[var "x"] .=>. Q[var "x"]) .|. (exists x. Q[var "x"] .&. P[var "x"]))
   .=>. (exists x. Q[var "x"] .&. P[var "x"])>>;;

let p26 = time splittab
 <<((exists x. P[var "x"]) .<=>. (exists x. Q[var "x"])) .&.
   (forall x y. P[var "x"] .&. Q[var "y"] .=>. (R[var "x"] .<=>. U[var "y"]))
   .=>. ((forall x. P[var "x"] .=>. R[var "x"]) .<=>. (forall x. Q[var "x"] .=>. U[var "x"]))>>;;

let p27 = time splittab
 <<(exists x. P[var "x"] .&. ~Q[var "x"]) .&.
   (forall x. P[var "x"] .=>. R[var "x"]) .&.
   (forall x. U[var "x"] .&. V[var "x"] .=>. P[var "x"]) .&.
   (exists x. R[var "x"] .&. ~Q[var "x"])
   .=>. (forall x. U[var "x"] .=>. ~R[var "x"])
       .=>. (forall x. U[var "x"] .=>. ~V[var "x"])>>;;

let p28 = time splittab
 <<(forall x. P[var "x"] .=>. (forall x. Q[var "x"])) .&.
   ((forall x. Q[var "x"] .|. R[var "x"]) .=>. (exists x. Q[var "x"] .&. R[var "x"])) .&.
   ((exists x. R[var "x"]) .=>. (forall x. L[var "x"] .=>. M[var "x"])) .=>.
   (forall x. P[var "x"] .&. L[var "x"] .=>. M[var "x"])>>;;

let p29 = time splittab
 <<(exists x. P[var "x"]) .&. (exists x. G[var "x"]) .=>.
   ((forall x. P[var "x"] .=>. H[var "x"]) .&. (forall x. G[var "x"] .=>. J[var "x"]) .<=>.
    (forall x y. P[var "x"] .&. G[var "y"] .=>. H[var "x"] .&. J[var "y"]))>>;;

let p30 = time splittab
 <<(forall x. P[var "x"] .|. G[var "x"] .=>. ~H[var "x"]) .&.
   (forall x. (G[var "x"] .=>. ~U[var "x"]) .=>. P[var "x"] .&. H[var "x"])
   .=>. (forall x. U[var "x"])>>;;

let p31 = time splittab
 <<~(exists x. P[var "x"] .&. (G[var "x"] .|. H[var "x"])) .&.
   (exists x. Q[var "x"] .&. P[var "x"]) .&.
   (forall x. ~H[var "x"] .=>. J[var "x"])
   .=>. (exists x. Q[var "x"] .&. J[var "x"])>>;;

let p32 = time splittab
 <<(forall x. P[var "x"] .&. (G[var "x"] .|. H[var "x"]) .=>. Q[var "x"]) .&.
   (forall x. Q[var "x"] .&. H[var "x"] .=>. J[var "x"]) .&.
   (forall x. R[var "x"] .=>. H[var "x"])
   .=>. (forall x. P[var "x"] .&. R[var "x"] .=>. J[var "x"])>>;;

let p33 = time splittab
 <<(forall x. P[var "a"] .&. (P[var "x"] .=>. P[var "b"]) .=>. P[var "c"]) .<=>.
   (forall x. P[var "a"] .=>. P[var "x"] .|. P[var "c"]) .&. (P[var "a"] .=>. P[var "b"] .=>. P[var "c"])>>;;

let p34 = time splittab
 <<((exists x. forall y. P[var "x"] .<=>. P[var "y"]) .<=>.
    ((exists x. Q[var "x"]) .<=>. (forall y. Q[var "y"]))) .<=>.
   ((exists x. forall y. Q[var "x"] .<=>. Q[var "y"]) .<=>.
    ((exists x. P[var "x"]) .<=>. (forall y. P[var "y"])))>>;;

let p35 = time splittab
 <<exists x y. P(x,y) .=>. (forall x y. P(x,y))>>;;

-- ------------------------------------------------------------------------- 
-- Full predicate logic (without identity and functions).                    
-- ------------------------------------------------------------------------- 

let p36 = time splittab
 <<(forall x. exists y. P(x,y)) .&.
   (forall x. exists y. G(x,y)) .&.
   (forall x y. P(x,y) .|. G(x,y)
   .=>. (forall z. P(y,z) .|. G(y,z) .=>. H(x,z)))
       .=>. (forall x. exists y. H(x,y))>>;;

let p37 = time splittab
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) .=>. P(y,w)) .&. P(y,z) .&.
     (P(y,w) .=>. (exists u. Q(u,w)))) .&.
   (forall x z. ~P(x,z) .=>. (exists y. Q(y,z))) .&.
   ((exists x y. Q(x,y)) .=>. (forall x. R(x,x))) .=>.
   (forall x. exists y. R(x,y))>>;;

let p38 = time splittab
 <<(forall x.
     P[var "a"] .&. (P[var "x"] .=>. (exists y. P[var "y"] .&. R(x,y))) .=>.
     (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))) .<=>.
   (forall x.
     (~P[var "a"] .|. P[var "x"] .|. (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))) .&.
     (~P[var "a"] .|. ~(exists y. P[var "y"] .&. R(x,y)) .|.
     (exists z w. P[var "z"] .&. R(x,w) .&. R(w,z))))>>;;

let p39 = time splittab
 <<~(exists x. forall y. P(y,x) .<=>. ~P(y,y))>>;;

let p40 = time splittab
 <<(exists y. forall x. P(x,y) .<=>. P(x,x))
  .=>. ~(forall x. exists y. forall z. P(z,y) .<=>. ~P(z,x))>>;;

let p41 = time splittab
 <<(forall z. exists y. forall x. P(x,y) .<=>. P(x,z) .&. ~P(x,x))
  .=>. ~(exists z. forall x. P(x,z))>>;;

let p42 = time splittab
 <<~(exists y. forall x. P(x,y) .<=>. ~(exists z. P(x,z) .&. P(z,x)))>>;;

let p43 = time splittab
 <<(forall x y. Q(x,y) .<=>. forall z. P(z,x) .<=>. P(z,y))
   .=>. forall x y. Q(x,y) .<=>. Q(y,x)>>;;

let p44 = time splittab
 <<(forall x. P[var "x"] .=>. (exists y. G[var "y"] .&. H(x,y)) .&.
   (exists y. G[var "y"] .&. ~H(x,y))) .&.
   (exists x. J[var "x"] .&. (forall y. G[var "y"] .=>. H(x,y))) .=>.
   (exists x. J[var "x"] .&. ~P[var "x"])>>;;

let p45 = time splittab
 <<(forall x.
     P[var "x"] .&. (forall y. G[var "y"] .&. H(x,y) .=>. J(x,y)) .=>.
       (forall y. G[var "y"] .&. H(x,y) .=>. R[var "y"])) .&.
   ~(exists y. L[var "y"] .&. R[var "y"]) .&.
   (exists x. P[var "x"] .&. (forall y. H(x,y) .=>.
     L[var "y"]) .&. (forall y. G[var "y"] .&. H(x,y) .=>. J(x,y))) .=>.
   (exists x. P[var "x"] .&. ~(exists y. G[var "y"] .&. H(x,y)))>>;;

let p46 = time splittab
 <<(forall x. P[var "x"] .&. (forall y. P[var "y"] .&. H(y,x) .=>. G[var "y"]) .=>. G[var "x"]) .&.
   ((exists x. P[var "x"] .&. ~G[var "x"]) .=>.
    (exists x. P[var "x"] .&. ~G[var "x"] .&.
               (forall y. P[var "y"] .&. ~G[var "y"] .=>. J(x,y)))) .&.
   (forall x y. P[var "x"] .&. P[var "y"] .&. H(x,y) .=>. ~J(y,x)) .=>.
   (forall x. P[var "x"] .=>. G[var "x"])>>;;

-- ------------------------------------------------------------------------- 
-- Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 
-- ------------------------------------------------------------------------- 

let p55 = time splittab
 <<lives(agatha) .&. lives(butler) .&. lives(charles) .&.
   (killed(agatha,agatha) .|. killed(butler,agatha) .|.
    killed(charles,agatha)) .&.
   (forall x y. killed(x,y) .=>. hates(x,y) .&. ~richer(x,y)) .&.
   (forall x. hates(agatha,x) .=>. ~hates(charles,x)) .&.
   (hates(agatha,agatha) .&. hates(agatha,charles)) .&.
   (forall x. lives[var "x"] .&. ~richer(x,agatha) .=>. hates(butler,x)) .&.
   (forall x. hates(agatha,x) .=>. hates(butler,x)) .&.
   (forall x. ~hates(x,agatha) .|. ~hates(x,butler) .|. ~hates(x,charles))
   .=>. killed(agatha,agatha) .&.
       ~killed(butler,agatha) .&.
       ~killed(charles,agatha)>>;;

let p57 = time splittab
 <<P(f([var "a"],b),f(b,c)) .&.
   P(f(b,c),f(a,c)) .&.
   (forall [var "x"] y z. P(x,y) .&. P(y,z) .=>. P(x,z))
   .=>. P(f(a,b),f(a,c))>>;;

-- ------------------------------------------------------------------------- 
-- See info-hol, circa 1500.                                                 
-- ------------------------------------------------------------------------- 

let p58 = time splittab
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
    ((P[var "x"] .&. Q[var "y"]) .=>. ((P[var "v"] .|. R[var "w"])  .&. (R[var "z"] .=>. Q[var "v"])))>>;;

let p59 = time splittab
 <<(forall x. P[var "x"] .<=>. ~P(f[var "x"])) .=>. (exists x. P[var "x"] .&. ~P(f[var "x"]))>>;;

let p60 = time splittab
 <<forall x. P(x,f[var "x"]) .<=>.
            exists y. (forall z. P(z,y) .=>. P(z,f[var "x"])) .&. P(x,y)>>;;

-- ------------------------------------------------------------------------- 
-- From Gilmore's classic paper.                                             
-- ------------------------------------------------------------------------- 

{- **** This is still too hard for us! Amazing...

let gilmore_1 = time splittab
 <<exists x. forall y z.
      ((F[var "y"] .=>. G[var "y"]) .<=>. F[var "x"]) .&.
      ((F[var "y"] .=>. H[var "y"]) .<=>. G[var "x"]) .&.
      (((F[var "y"] .=>. G[var "y"]) .=>. H[var "y"]) .<=>. H[var "x"])
      .=>. F[var "z"] .&. G[var "z"] .&. H[var "z"]>>;;

 ***** -}

{- ** This is not valid, according to Gilmore

let gilmore_2 = time splittab
 <<exists x y. forall z.
        (F(x,z) .<=>. F(z,y)) .&. (F(z,y) .<=>. F(z,z)) .&. (F(x,y) .<=>. F(y,x))
        .=>. (F(x,y) .<=>. F(x,z))>>;;

 ** -}

let gilmore_3 = time splittab
 <<exists x. forall y z.
        ((F(y,z) .=>. (G[var "y"] .=>. H[var "x"])) .=>. F(x,x)) .&.
        ((F(z,x) .=>. G[var "x"]) .=>. H[var "z"]) .&.
        F(x,y)
        .=>. F(z,z)>>;;

let gilmore_4 = time splittab
 <<exists x y. forall z.
        (F(x,y) .=>. F(y,z) .&. F(z,z)) .&.
        (F(x,y) .&. G(x,y) .=>. G(x,z) .&. G(z,z))>>;;

let gilmore_5 = time splittab
 <<(forall x. exists y. F(x,y) .|. F(y,x)) .&.
   (forall x y. F(y,x) .=>. F(y,y))
   .=>. exists z. F(z,z)>>;;

let gilmore_6 = time splittab
 <<forall x. exists y.
        (exists u. forall v. F(u,x) .=>. G(v,u) .&. G(u,x))
        .=>. (exists u. forall v. F(u,y) .=>. G(v,u) .&. G(u,y)) .|.
            (forall u v. exists w. G(v,u) .|. H(w,y,u) .=>. G(u,w))>>;;

let gilmore_7 = time splittab
 <<(forall x. K[var "x"] .=>. exists y. L[var "y"] .&. (F(x,y) .=>. G(x,y))) .&.
   (exists z. K[var "z"] .&. forall u. L[var "u"] .=>. F(z,u))
   .=>. exists v w. K[var "v"] .&. L[var "w"] .&. G(v,w)>>;;

let gilmore_8 = time splittab
 <<exists x. forall y z.
        ((F(y,z) .=>. (G[var "y"] .=>. (forall u. exists v. H(u,v,x)))) .=>. F(x,x)) .&.
        ((F(z,x) .=>. G[var "x"]) .=>. (forall u. exists v. H(u,v,z))) .&.
        F(x,y)
        .=>. F(z,z)>>;;

let gilmore_9 = time splittab
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) .&. G(y,u) .&. ~H(y,x))
          .=>. (forall u. exists v. F(x,u,v) .&. G(z,u) .&. ~H(x,z))
          .=>. (forall u. exists v. F(x,u,v) .&. G(y,u) .&. ~H(x,y))) .&.
        ((forall u. exists v. F(x,u,v) .&. G(y,u) .&. ~H(x,y))
         .=>. ~(forall u. exists v. F(x,u,v) .&. G(z,u) .&. ~H(x,z))
         .=>. (forall u. exists v. F(y,u,v) .&. G(y,u) .&. ~H(y,x)) .&.
             (forall u. exists v. F(z,u,v) .&. G(y,u) .&. ~H(z,y)))>>;;

-- ------------------------------------------------------------------------- 
-- Example from Davis-Putnam papers where Gilmore procedure is poor.         
-- ------------------------------------------------------------------------- 

let davis_putnam_example = time splittab
 <<exists x. exists y. forall z.
        (F(x,y) .=>. (F(y,z) .&. F(z,z))) .&.
        ((F(x,y) .&. G(x,y)) .=>. (G(x,z) .&. G(z,z)))>>;;

************ -}
-}
