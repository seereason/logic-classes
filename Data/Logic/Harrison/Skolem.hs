{-# LANGUAGE CPP, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Harrison.Skolem
#if 1
    ( module Skolem
    ) where

import Skolem
#else
    ( simplify
    -- , simplify'
    , lsimplify
    , nnf
    -- , nnf'
    , pnf
    -- , pnf'
    , functions
    -- , functions'
    , SkolemT
    , Skolem
    , runSkolem
    , runSkolemT
    , specialize
    , skolemize
    -- , literal
    , askolemize
    , skolemNormalForm
    -- , prenex'
    , skolem
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT(runStateT))
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..), binop)
import Data.Logic.Classes.Constants (HasBoolean(fromBool, asBool), true, false)
import Data.Logic.Classes.FirstOrder (IsQuantified(quant, foldQuantified), exists, for_all, Quant(..), quant, toPropositional)
import Data.Logic.Classes.Formula (IsFormula(..))
import Data.Logic.Classes.Literal (IsLiteral(foldLiteral))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Propositional (IsPropositional(..))
import qualified Data.Logic.Classes.Skolem as C
import Data.Logic.Classes.Term (IsTerm(..))
import Data.Logic.Classes.Variable (IsVariable(variant))
import Data.Logic.Harrison.FOL (fv, subst)
import Data.Logic.Harrison.Lib ((|=>))
import qualified Data.Map as Map
import qualified Data.Set as Set

-- =========================================================================
-- Prenex and Skolem normal forms.                                           
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- Routine simplification. Like "psimplify" but with quantifier clauses.     
-- ------------------------------------------------------------------------- 

simplify1 :: (IsQuantified fof atom v,
              -- Formula fof term v,
              Atom atom term v,
              IsTerm term v f) => fof -> fof
simplify1 fm =
    foldQuantified qu co tf at fm
    where
      qu _ x p = if Set.member x (fv p) then fm else p
      co ((:~:) p) = foldQuantified (\ _ _ _ -> fm) nco (fromBool . not) (\ _ -> fm) p
      co (BinOp l op r) = simplifyBinop l op r
      nco ((:~:) p) = p
      nco _ = fm
      tf = fromBool
      at _ = fm

simplifyBinop :: forall p. (HasBoolean p, IsCombinable p) => p -> BinOp -> p -> p
simplifyBinop l op r =
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
      (Just False, (:<=>:), Just False) -> true
      (Just True,  (:<=>:), _         ) -> r
      (Just False, (:<=>:), _         ) -> (.~.) r
      (_,          (:<=>:), Just True ) -> l
      (_,          (:<=>:), Just False) -> (.~.) l
      _ -> binop l op r

simplify :: (IsQuantified fof atom v,
             Atom atom term v,
             IsTerm term v f) => fof -> fof
simplify fm =
    foldQuantified qu co tf at fm
    where
      qu op x fm' = simplify1 (quant op x (simplify fm'))
      co ((:~:) fm') = simplify1 ((.~.) (simplify fm'))
      co (BinOp fm1 op fm2) = simplify1 (binop (simplify fm1) op (simplify fm2))
      tf = fromBool
      at _ = fm

-- | Just looks for double negatives and negated constants.
lsimplify :: IsLiteral lit atom => lit -> lit
lsimplify fm = foldLiteral (lsimplify1 . (.~.) . lsimplify) fromBool (const fm) fm

lsimplify1 :: IsLiteral lit atom => lit -> lit
lsimplify1 fm = foldLiteral (foldLiteral id (fromBool . not) (const fm)) fromBool (const fm) fm


-- ------------------------------------------------------------------------- 
-- Negation normal form.                                                     
-- ------------------------------------------------------------------------- 

nnf :: IsQuantified formula atom v => formula -> formula
nnf fm =
    foldQuantified nnfQuant nnfCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      nnfQuant op v p = quant op v (nnf p)
      nnfCombine ((:~:) p) = foldQuantified nnfNotQuant nnfNotCombine (fromBool . not) (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q
      nnfNotQuant (:!:) v p = exists v (nnf ((.~.) p))
      nnfNotQuant (:?:) v p = for_all v (nnf ((.~.) p))
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

-- ------------------------------------------------------------------------- 
-- Prenex normal form.                                                       
-- ------------------------------------------------------------------------- 

pullQuants :: forall formula atom v term f. (IsQuantified formula atom v, {-Formula formula term v,-} Atom atom term v, IsTerm term v f) =>
              formula -> formula
pullQuants fm =
    foldQuantified (\ _ _ _ -> fm) pullQuantsCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      getQuant = foldQuantified (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing)
      pullQuantsCombine ((:~:) _) = fm
      pullQuantsCombine (BinOp l op r) = 
          case (getQuant l, op, getQuant r) of
            (Just ((:!:), vl, l'), (:&:), Just ((:!:), vr, r')) -> pullq True  True  fm for_all (.&.) vl vr l' r'
            (Just ((:?:), vl, l'), (:|:), Just ((:?:), vr, r')) -> pullq True  True  fm exists  (.|.) vl vr l' r'
            (Just ((:!:), vl, l'), (:&:), _)                     -> pullq True  False fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just ((:!:), vr, r')) -> pullq False True  fm for_all (.&.) vr vr l  r'
            (Just ((:!:), vl, l'), (:|:), _)                     -> pullq True  False fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just ((:!:), vr, r')) -> pullq False True  fm for_all (.|.) vr vr l  r'
            (Just ((:?:), vl, l'), (:&:), _)                     -> pullq True  False fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just ((:?:), vr, r')) -> pullq False True  fm exists  (.&.) vr vr l  r'
            (Just ((:?:), vl, l'), (:|:), _)                     -> pullq True  False fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just ((:?:), vr, r')) -> pullq False True  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: (IsQuantified formula atom v, Atom atom term v, IsTerm term v f) =>
         Bool -> Bool
      -> formula
      -> (v -> formula -> formula)
      -> (formula -> formula -> formula)
      -> v -> v
      -> formula -> formula
      -> formula
pullq l r fm mkq op x y p q =
    let z = variant x (fv fm)
        p' = if l then subst (x |=> vt z) p else p
        q' = if r then subst (y |=> vt z) q else q
        fm' = pullQuants (op p' q') in
    mkq z fm'

-- |Recursivly apply pullQuants anywhere a quantifier might not be
-- leftmost.
prenex :: (IsQuantified formula atom v, {-Formula formula term v,-} Atom atom term v, IsTerm term v f) =>
          formula -> formula 
prenex fm =
    foldQuantified qu co (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      co (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      co _ = fm

-- |Convert to Prenex normal form, with all quantifiers at the left.
pnf :: (IsQuantified formula atom v, Atom atom term v, IsTerm term v f) => formula -> formula
pnf = prenex . nnf . simplify

-- ------------------------------------------------------------------------- 
-- Get the functions in a term and formula.                                  
-- ------------------------------------------------------------------------- 

-- FIXME: the function parameter should be a method in the Atom class,
-- but we need to add a type parameter f to it first.
functions :: forall formula atom f. (IsFormula formula atom, Ord f) => (atom -> Set.Set (f, Int)) -> formula -> Set.Set (f, Int)
-- functions fa fm = foldAtoms (\ s a -> Set.union s (fa a)) Set.empty fm
functions fa fm = overatoms (\ a s -> Set.union s (fa a)) fm Set.empty

-- ------------------------------------------------------------------------- 
-- State monad for generating Skolem functions and constants.
-- ------------------------------------------------------------------------- 

-- | Harrison's code generated skolem functions by adding a prefix to
-- the variable name they are based on.  Here we have a more general
-- and type safe solution: we require that variables be instances of
-- class Skolem which creates Skolem functions based on an integer.
-- This state value exists in the SkolemT monad during skolemization
-- and tracks the next available number and the current list of
-- universally quantified variables.

data SkolemState v term
    = SkolemState
      { skolemCount :: Int
        -- ^ The next available Skolem number.
      , univQuant :: [v]
        -- ^ The variables which are universally quantified in the
        -- current scope, in the order they were encountered.  During
        -- Skolemization these are the parameters passed to the Skolem
        -- function.
      }

-- | The state associated with the Skolem monad.
newSkolemState :: SkolemState v term
newSkolemState
    = SkolemState
      { skolemCount = 1
      , univQuant = []
      }

-- | The Skolem monad transformer
type SkolemT v term m = StateT (SkolemState v term) m

-- | Run a computation in the Skolem monad.
runSkolem :: SkolemT v term Identity a -> a
runSkolem = runIdentity . runSkolemT

-- | The Skolem monad
type Skolem v term = StateT (SkolemState v term) Identity

-- | Run a computation in a stacked invocation of the Skolem monad.
runSkolemT :: Monad m => SkolemT v term m a -> m a
runSkolemT action = (runStateT action) newSkolemState >>= return . fst

-- ------------------------------------------------------------------------- 
-- Core Skolemization function.                                              
-- ------------------------------------------------------------------------- 

-- |Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the SkolemT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (Monad m,
           IsQuantified fof atom v,
           -- IsPropositional pf atom,
           -- Formula formula term v,
           Atom atom term v,
           IsTerm term v f) =>
          fof -> SkolemT v term m fof
skolem fm =
    foldQuantified qu co (return . fromBool) (return . atomic) fm
    where
      -- We encountered an existentially quantified variable y,
      -- allocate a new skolem function fx and do a substitution to
      -- replace occurrences of y with fx.  The value of the Skolem
      -- function is assumed to equal the value of y which satisfies
      -- the formula.
      qu (:?:) y p =
          do let xs = fv fm
             let fx = fApp (C.toSkolem y) (map vt (Set.toAscList xs))
             skolem (subst (Map.singleton y fx) p)
      qu (:!:) x p = skolem p >>= return . for_all x
      co (BinOp l (:&:) r) = skolem2 (.&.) l r
      co (BinOp l (:|:) r) = skolem2 (.|.) l r
      co _ = return fm

skolem2 :: (Monad m,
            IsQuantified fof atom v,
            -- IsPropositional pf atom,
            -- Formula formula term v,
            Atom atom term v,
            IsTerm term v f) =>
           (fof -> fof -> fof) -> fof -> fof -> SkolemT v term m fof
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- ------------------------------------------------------------------------- 
-- Overall Skolemization function.                                           
-- ------------------------------------------------------------------------- 

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: forall m fof atom term v f.
              (Monad m,
               IsQuantified fof atom v,
               Atom atom term v,
               IsTerm term v f) =>
              fof -> SkolemT v term m fof
askolemize = skolem . nnf . simplify

-- | Remove the leading universal quantifiers.  After a call to pnf
-- this will be all the universal quantifiers, and the skolemization
-- will have already turned all the existential quantifiers into
-- skolem functions.
specialize :: forall fof atom v. IsQuantified fof atom v => fof -> fof
specialize f =
    foldQuantified q (\ _ -> f) (\ _ -> f) (\ _ -> f) f
    where
      q (:!:) _ f' = specialize f'
      q _ _ _ = f

-- | Skolemize and then specialize.  Because we know all quantifiers
-- are gone we can convert to any instance of IsPropositional.
skolemize :: forall m fof atom term v f pf atom2. (Monad m,
              IsQuantified fof atom v,
              IsPropositional pf atom2,
              Atom atom term v,
              IsTerm term v f,
              Eq pf) =>
             (atom -> atom2) -> fof -> SkolemT v term m pf
skolemize ca fm = askolemize fm >>= return . (toPropositional ca :: fof -> pf) . specialize . pnf

{-
-- | Convert a first order formula into a disjunct of conjuncts of
-- literals.  Note that this can convert any instance of
-- IsQuantified into any instance of IsLiteral.
literal :: forall fof atom term v p f lit. (IsLiteral fof atom, Apply atom p term, Term term v f, IsLiteral lit atom, Formula lit atom, Ord lit) =>
           fof -> Set.Set (Set.Set lit)
literal fm =
    foldLiteral neg tf at fm
    where
      neg :: fof -> Set.Set (Set.Set lit)
      neg x = Set.map (Set.map (.~.)) (literal x)
      tf = Set.singleton . Set.singleton . fromBool
      at :: atom -> Set.Set (Set.Set lit)
      at x = foldApply (\ _ _ -> Set.singleton (Set.singleton (atomic x))) tf x
-}

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (IsQuantified fof atom v,
                     IsPropositional pf atom2,
                     -- Formula fof term v,
                     -- Formula pf term v,
                     Atom atom term v,
                     IsTerm term v f,
                     Monad m, Ord fof, Eq pf) =>
                    (atom -> atom2) -> fof -> SkolemT v term m pf
skolemNormalForm = skolemize
#endif
