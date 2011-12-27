{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Harrison.Skolem
    ( simplify
    , nnf
    , pnf
    , functions
    , skolemize
    , specialize
    , askolemize
    , literal
    ) where

import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..), binop)
import Data.Logic.Classes.Constants (true, false)
import Data.Logic.Classes.Equals (AtomEq(foldAtomEq))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(exists, for_all, foldFirstOrder), Quant(..), quant)
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(..), Function(variantF))
import Data.Logic.Classes.Variable (Variable(variant))
import Data.Logic.Harrison.FOL (fv, subst)
import Data.Logic.Harrison.Lib ((|=>))
import qualified Data.Set as Set

-- =========================================================================
-- Prenex and Skolem normal forms.                                           
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- Routine simplification. Like "psimplify" but with quantifier clauses.     
-- ------------------------------------------------------------------------- 

simplify1 :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f) => fof -> fof
simplify1 fm =
    foldFirstOrder qu co pr fm
    where
      qu _ x p = if Set.member x (fv p) then fm else p
      co TRUE = fm
      co FALSE = fm
      co ((:~:) p) = foldFirstOrder (\ _ _ _ -> fm) nco (\ _ -> fm) p
      co (BinOp l op r) =
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
      nco TRUE = false
      nco FALSE = true
      nco ((:~:) p) = p
      nco _ = fm
      testBool = foldFirstOrder (\ _ _ _ -> Nothing) (\ x -> case x of TRUE -> Just True; FALSE -> Just False; _ -> Nothing) (\ _ -> Nothing)
      pr _ = fm

simplify :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f) => fof -> fof
simplify fm =
    foldFirstOrder q c p fm
    where
      q op x fm' = simplify1 (quant op x (simplify fm'))
      c ((:~:) fm') = simplify1 ((.~.) (simplify fm'))
      c (BinOp fm1 op fm2) = simplify1 (binop (simplify fm1) op (simplify fm2))
      c FALSE = false
      c TRUE = true
      p _ = fm

-- ------------------------------------------------------------------------- 
-- Negation normal form.                                                     
-- ------------------------------------------------------------------------- 

nnf :: FirstOrderFormula formula atom v => formula -> formula
nnf fm =
    foldFirstOrder nnfQuant nnfCombine (\ _ -> fm) fm
    where
      nnfQuant op v p = quant op v (nnf p)
      nnfCombine ((:~:) p) = foldFirstOrder nnfNotQuant nnfNotCombine (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q
      nnfCombine TRUE = true
      nnfCombine FALSE = false
      nnfNotQuant Forall v p = exists v (nnf ((.~.) p))
      nnfNotQuant Exists v p = for_all v (nnf ((.~.) p))
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q
      nnfNotCombine TRUE = false
      nnfNotCombine FALSE = true

-- ------------------------------------------------------------------------- 
-- Prenex normal form.                                                       
-- ------------------------------------------------------------------------- 

pullQuants :: forall formula atom v term p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> formula
pullQuants fm =
    foldFirstOrder (\ _ _ _ -> fm) pullQuantsCombine (\ _ -> fm) fm
    where
      getQuant = foldFirstOrder (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing)
      pullQuantsCombine ((:~:) _) = fm
      pullQuantsCombine (BinOp l op r) = 
          case (getQuant l, op, getQuant r) of
            (Just (Forall, vl, l'), (:&:), Just (Forall, vr, r')) -> pullq True  True  fm for_all (.&.) vl vr l' r'
            (Just (Exists, vl, l'), (:|:), Just (Exists, vr, r')) -> pullq True  True  fm exists  (.|.) vl vr l' r'
            (Just (Forall, vl, l'), (:&:), _)                     -> pullq True  False fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just (Forall, vr, r')) -> pullq False True  fm for_all (.&.) vr vr l  r'
            (Just (Forall, vl, l'), (:|:), _)                     -> pullq True  False fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just (Forall, vr, r')) -> pullq False True  fm for_all (.|.) vr vr l  r'
            (Just (Exists, vl, l'), (:&:), _)                     -> pullq True  False fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.&.) vr vr l  r'
            (Just (Exists, vl, l'), (:|:), _)                     -> pullq True  False fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm
      pullQuantsCombine _ = error "Unsimplified formula passed to pullQuants"

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) =>
         Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> formula
pullq l r fm mkq op x y p q =
    let z = variant x (fv fm)
        p' = if l then subst (x |=> vt z) p else p
        q' = if r then subst (y |=> vt z) q else q
        fm' = pullQuants (op p' q') in
    mkq z fm'

-- |Recursivly apply pullQuants anywhere a quantifier might not be
-- leftmost.
prenex :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> formula 
prenex fm =
    foldFirstOrder q c (\ _ -> fm) fm
    where
      q op x p = quant op x (prenex p)
      c (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      c (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      c _ = fm

-- |Convert to Prenex normal form, with all quantifiers at the left.
pnf :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> formula
pnf = prenex . nnf . simplify

-- ------------------------------------------------------------------------- 
-- Get the functions in a term and formula.                                  
-- ------------------------------------------------------------------------- 

funcs :: (Term term v f, Ord f) => term -> Set.Set (f, Int)
funcs tm =
    foldTerm (const Set.empty)
             (\ f args -> foldr (\ arg r -> Set.union (funcs arg) r) (Set.singleton (f, length args)) args)
             tm

functions :: forall fof atom term v p f. (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Eq f, Ord f) => fof -> Set.Set (f, Int)
functions fm =
    foldFirstOrder qu co pr fm
    where
      qu _ _ p = functions p
      co ((:~:) p) = functions p
      co (BinOp p _ q) = Set.union (functions p) (functions q)
      co _ = error "Unsimplified formula passed to functions"
      pr = foldAtomEq (\ _ ts -> Set.unions (map funcs ts)) (\ t1 t2 -> Set.union (funcs t1) (funcs t2))
    -- atom_union (\ (R p a) -> foldr (Set.union . funcs) Set.empty a) fm

-- ------------------------------------------------------------------------- 
-- Core Skolemization function.                                              
-- ------------------------------------------------------------------------- 

skolem :: forall fof atom term v p f. (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Ord f) => fof -> Set.Set f -> (fof, Set.Set f)
skolem fm fns =
    foldFirstOrder qu co pr fm
    where
      qu :: Quant -> v -> fof -> (fof, Set.Set f)
      qu Exists y p =
        let xs = fv fm in
        let f = variantF (if Set.null xs then skolemConstant (undefined :: term) y else skolemFunction (undefined :: term) y) fns in
        let fx = fApp f (map vt (Set.toList xs)) in
        skolem (subst (y |=> fx) p) (Set.insert f fns)
      qu Forall x p =
          let (p',fns') = skolem p fns in (for_all x p', fns')
      co :: Combination fof -> (fof, Set.Set f)
      co (BinOp p (:&:) q) = skolem2 (.&.) (p,q) fns
      co (BinOp p (:|:) q) = skolem2 (.|.) (p,q) fns
      co _ = (fm,fns)
      pr :: atom -> (fof, Set.Set f)
      pr _ = (fm,fns)

      skolem2 :: (fof -> fof -> fof) -> (fof, fof) -> Set.Set f -> (fof, Set.Set f)
      skolem2 cons (p,q) fns' =
          let (p',fns'') = skolem p fns' in
          let (q',fns''') = skolem q fns'' in
          (cons p' q', fns''')

-- ------------------------------------------------------------------------- 
-- Overall Skolemization function.                                           
-- ------------------------------------------------------------------------- 

askolemize :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f) => fof -> fof
askolemize fm =
  fst(skolem (nnf(simplify fm)) (Set.map fst (functions fm)));;

-- | Drop all universal quantifiers.
specialize :: FirstOrderFormula fof atom v => fof -> fof
specialize fm =
    foldFirstOrder q (\ _ -> fm) (\ _ -> fm) fm
    where
      q Forall _ p = specialize p
      q _ _ _ = fm

skolemize :: (FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f) => fof -> fof
skolemize fm = {- t1 $ -} specialize . pnf . askolemize $ fm
    -- where t1 x = trace ("skolemize: " ++ show fm ++ "\n        -> " ++ show x) x

-- | Convert a first order formula into a disjunct of conjuncts of
-- literals.  Note that this can convert any instance of
-- FirstOrderFormula into any instance of Literal.
literal :: (FirstOrderFormula fof atom v, Atom atom p term, Term term v f, Literal lit atom v, Ord lit) =>
           fof -> Set.Set (Set.Set lit)
literal fm =
    foldFirstOrder (error "quantifier") co pr fm
    where
      pr x = Set.singleton (Set.singleton (atomic x))
      co ((:~:) x) = Set.map (Set.map (.~.)) (literal x)
      co (BinOp p (:|:) q) = Set.singleton (Set.unions (Set.toList (literal p) ++ Set.toList (literal q)))
          -- Set.singleton (Set.union (flatten (literal p)) (flatten (literal q)))
          -- where flatten = Set.fold Set.union Set.empty
      co (BinOp p (:&:) q) = Set.union (literal p) (literal q)
      co TRUE = Set.singleton (Set.singleton true)
      co FALSE = Set.singleton (Set.singleton false)
      co _ = error "literal"
