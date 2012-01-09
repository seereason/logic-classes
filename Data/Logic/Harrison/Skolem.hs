{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Harrison.Skolem
    ( simplify
    , lsimplify
    , nnf
    , pnf
    , functions
    , SkolemT
    , runSkolem
    , runSkolemT
    , specialize
    , skolemize
    , literal
    , askolemize
    , skolemNormalForm
    -- , substituteEq
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT(runStateT), get, put)
import Data.Logic.Classes.Apply (Apply(foldApply))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..), binop)
import Data.Logic.Classes.Constants (Constants(fromBool, true, false), asBool)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(exists, for_all, foldFirstOrder), Quant(..), quant)
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Literal (Literal(foldLiteral, atomic))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Skolem (Skolem(toSkolem))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Classes.Variable (Variable(variant))
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

simplify1 :: (FirstOrderFormula fof atom v, Formula atom term v, Term term v f, Eq fof) =>
             fof -> fof
simplify1 fm =
    foldFirstOrder qu co tf at fm
    where
      qu _ x p = if Set.member x (fv p) then fm else p
      co ((:~:) p) = foldFirstOrder (\ _ _ _ -> fm) nco (fromBool . not) (\ _ -> fm) p
      co (BinOp l op r) =
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
      nco ((:~:) p) = p
      nco _ = fm
      tf = fromBool
      at _ = fm

simplify :: (FirstOrderFormula fof atom v, Formula atom term v, Term term v f, Eq fof) =>
            fof -> fof
simplify fm =
    foldFirstOrder qu co tf at fm
    where
      qu op x fm' = simplify1 (quant op x (simplify fm'))
      co ((:~:) fm') = simplify1 ((.~.) (simplify fm'))
      co (BinOp fm1 op fm2) = simplify1 (binop (simplify fm1) op (simplify fm2))
      tf = fromBool
      at _ = fm

-- | Just looks for double negatives and negated constants.
lsimplify :: Literal lit atom v => lit -> lit
lsimplify fm = foldLiteral (lsimplify1 . (.~.) . lsimplify) fromBool (const fm) fm

lsimplify1 :: Literal lit atom v => lit -> lit
lsimplify1 fm = foldLiteral (foldLiteral id (fromBool . not) (const fm)) fromBool (const fm) fm


-- ------------------------------------------------------------------------- 
-- Negation normal form.                                                     
-- ------------------------------------------------------------------------- 

nnf :: FirstOrderFormula formula atom v => formula -> formula
nnf fm =
    foldFirstOrder nnfQuant nnfCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      nnfQuant op v p = quant op v (nnf p)
      nnfCombine ((:~:) p) = foldFirstOrder nnfNotQuant nnfNotCombine (fromBool . not) (\ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q
      nnfNotQuant Forall v p = exists v (nnf ((.~.) p))
      nnfNotQuant Exists v p = for_all v (nnf ((.~.) p))
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

-- ------------------------------------------------------------------------- 
-- Prenex normal form.                                                       
-- ------------------------------------------------------------------------- 

pullQuants :: forall formula atom v term f. (FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
              formula -> formula
pullQuants fm =
    foldFirstOrder (\ _ _ _ -> fm) pullQuantsCombine (\ _ -> fm) (\ _ -> fm) fm
    where
      getQuant = foldFirstOrder (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing)
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

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: (FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
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
prenex :: (FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
          formula -> formula 
prenex fm =
    foldFirstOrder qu co (\ _ -> fm) (\ _ -> fm) fm
    where
      qu op x p = quant op x (prenex p)
      co (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      co (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      co _ = fm

-- |Convert to Prenex normal form, with all quantifiers at the left.
pnf :: (FirstOrderFormula formula atom v, Formula atom term v, Term term v f, Eq formula) =>
       formula -> formula
pnf = prenex . nnf . simplify

-- ------------------------------------------------------------------------- 
-- Get the functions in a term and formula.                                  
-- ------------------------------------------------------------------------- 

functions :: forall formula atom v f. (FirstOrderFormula formula atom v, Ord f) => (atom -> Set.Set (f, Int)) -> formula -> Set.Set (f, Int)
functions fa fm =
    foldFirstOrder qu co tf fa fm
    where
      qu _ _ p = functions fa p
      co ((:~:) p) = functions fa p
      co (BinOp p _ q) = Set.union (functions fa p) (functions fa q)
      tf _ = Set.empty

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
      -- , skolemMap :: Map.Map v term
      --   -- ^ Map from variables to applications of a Skolem function
      , univQuant :: [v]
        -- ^ The variables which are universally quantified in the
        -- current scope, in the order they were encountered.  During
        -- Skolemization these are the parameters passed to the Skolem
        -- function.
      }

newSkolemState :: SkolemState v term
newSkolemState = SkolemState { skolemCount = 1
                             -- , skolemMap = Map.empty
                             , univQuant = [] }

type SkolemT v term m = StateT (SkolemState v term) m

runSkolem :: SkolemT v term Identity a -> a
runSkolem = runIdentity . runSkolemT

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
skolem :: (Monad m, FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
          formula -> SkolemT v term m formula
skolem fm =
    foldFirstOrder qu co (\ _ -> return fm) (\ _ -> return fm) fm
    where
      qu Exists y p =
          do let xs = fv fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map vt (Set.toList xs))
             skolem (subst (Map.singleton y fx) p)
      qu Forall x p = skolem p >>= return . for_all x
      co (BinOp l (:&:) r) = skolem2 (.&.) l r
      co (BinOp l (:|:) r) = skolem2 (.|.) l r
      co _ = return fm

skolem2 :: (Monad m, FirstOrderFormula formula atom v, Formula atom term v, Term term v f) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

-- ------------------------------------------------------------------------- 
-- Overall Skolemization function.                                           
-- ------------------------------------------------------------------------- 

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: (Monad m, FirstOrderFormula formula atom v, Formula atom term v, Term term v f, Eq formula) =>
              formula -> SkolemT v term m formula
askolemize = skolem . nnf . simplify

specialize :: forall fof atom v. FirstOrderFormula fof atom v => fof -> fof
specialize f =
    foldFirstOrder q (\ _ -> f) (\ _ -> f) (\ _ -> f) f
    where
      q Forall _ f' = specialize f'
      q _ _ _ = f

skolemize :: (Monad m, FirstOrderFormula fof atom v, Formula atom term v, Term term v f, Eq fof) =>
             fof -> SkolemT v term m fof
skolemize fm = askolemize fm >>= return . specialize . pnf

-- | Convert a first order formula into a disjunct of conjuncts of
-- literals.  Note that this can convert any instance of
-- FirstOrderFormula into any instance of Literal.
literal :: forall fof atom term v p f lit. (Literal fof atom v, Apply atom p term, Term term v f, Literal lit atom v, Ord lit) =>
           fof -> Set.Set (Set.Set lit)
literal fm =
    foldLiteral neg tf at fm
    where
      neg :: fof -> Set.Set (Set.Set lit)
      neg x = Set.map (Set.map (.~.)) (literal x)
      tf = Set.singleton . Set.singleton . fromBool
      at :: atom -> Set.Set (Set.Set lit)
      at x = foldApply (\ _ _ -> Set.singleton (Set.singleton (Data.Logic.Classes.Literal.atomic x))) tf x

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (FirstOrderFormula fof atom v,
                     Formula atom term v,
                     Term term v f,
                     Monad m, Eq fof) =>
                    fof -> SkolemT v term m fof
skolemNormalForm f = askolemize f >>= return . specialize . pnf
