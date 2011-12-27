{-# LANGUAGE PackageImports, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Skolem
    ( LiteralMapT
    , NormalT
    , runNormalT
    , runNormal
    , NormalT'
    , runNormalT'
    , runNormal'
    , skolemNormalForm
    ) where

import "mtl" Control.Monad.Identity (Identity(runIdentity))
import "mtl" Control.Monad.State (StateT(runStateT), get, put)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.FirstOrderEq (substituteEq)
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Classes.Skolem (Skolem(toSkolem))
import Data.Logic.Harrison.FOL (fv)
import Data.Logic.Normal.Negation (negationNormalForm)
import Data.Logic.Normal.Prenex (prenexNormalForm)
import qualified Data.Map as Map
import qualified Data.Set as Set
 
--type LiteralMap f = LiteralMapT f Identity
type LiteralMapT f = StateT (Int, Map.Map f Int)

--runLiteralMap :: LiteralMap p a -> a
--runLiteralMap action = runIdentity (runLiteralMapM action)

runLiteralMapM :: Monad m => LiteralMapT f m a -> m a
runLiteralMapM action = (runStateT action) (1, Map.empty) >>= return . fst

-- |The logic monad contains (will contain) several types of state to
-- support the operations done on logic formulas: Skolemization,
-- literal substitution, and the set of support during a proof
-- procedure.
data LogicState v term
    = LogicState
      { skolemCount :: Int
        -- ^ The next available Skolem number.
      , skolemMap :: Map.Map v term
        -- ^ Map from variables to applications of a Skolem function
      , univQuant :: [v]
        -- ^ The variables which are universally quantified in the
        -- current scope, in the order they were encountered.  During
        -- Skolemization these are the parameters passed to the Skolem
        -- function.
      }

newLogicState :: LogicState v term
newLogicState = LogicState { skolemCount = 1
                           , skolemMap = Map.empty
                           , univQuant = [] }

type NormalT v term m = StateT (LogicState v term) m

runNormalT :: Monad m => NormalT v term m a -> m a
runNormalT action = (runStateT action) newLogicState >>= return . fst

runNormal :: NormalT v term Identity a -> a
runNormal = runIdentity . runNormalT

-- |Combination of Normal monad and LiteralMap monad
type NormalT' formula v term m a = NormalT v term (LiteralMapT formula m) a

runNormalT' :: Monad m => NormalT' formula v term m a -> m a
runNormalT' action = runLiteralMapM (runNormalT action)

runNormal' :: NormalT' formula v term Identity a -> a
runNormal' = runIdentity . runNormalT'

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> NormalT v term m formula
skolemNormalForm f = askolemize f >>= return . specialize . prenexNormalForm

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> NormalT v term m formula
askolemize = skolem . negationNormalForm {- nnf . simplify -}

-- |Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the NormalT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> NormalT v term m formula
skolem fm =
    foldFirstOrder q c (\ _ -> return fm) fm
    where
      q Exists y p =
          do let xs = fv fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map vt (Set.toList xs))
             skolem (substituteEq y fx p)
      q Forall x p = skolem p >>= return . for_all x
      c (BinOp l (:&:) r) = skolem2 (.&.) l r
      c (BinOp l (:|:) r) = skolem2 (.|.) l r
      c _ = return fm

skolem2 :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) =>
           (formula -> formula -> formula) -> formula -> formula -> NormalT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

specialize :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> formula
specialize f =
    foldFirstOrder q (\ _ -> f) (\ _ -> f) f
    where
      q Forall _ f' = specialize f'
      q _ _ _ = f
