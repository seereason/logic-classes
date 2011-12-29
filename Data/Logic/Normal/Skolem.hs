{-# LANGUAGE PackageImports, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Skolem
    ( LiteralMapT
    , SkolemT
    , runSkolemT
    , runSkolem
    , NormalT
    , runNormalT
    , runNormal
    , specialize
    , skolemize
    , literal
    , askolemize
    , skolemNormalForm
    ) where

import "mtl" Control.Monad.Identity (Identity(runIdentity))
import "mtl" Control.Monad.State (StateT(runStateT), get, put)
import Data.Logic.Classes.Atom (Atom(foldAtom))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (fromBool)
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.FirstOrderEq (substituteEq)
import Data.Logic.Classes.Literal (Literal(foldLiteral, atomic))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Classes.Skolem (Skolem(toSkolem))
import Data.Logic.Harrison.FOL (fv)
import Data.Logic.Harrison.Skolem (pnf)
import Data.Logic.Normal.Negation (negationNormalForm)
import Data.Logic.Normal.Prenex (prenexNormalForm)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- |Combination of Normal monad and LiteralMap monad
type NormalT formula v term m a = SkolemT v term (LiteralMapT formula m) a

runNormalT :: Monad m => NormalT formula v term m a -> m a
runNormalT action = runLiteralMapM (runSkolemT action)

runNormal :: NormalT formula v term Identity a -> a
runNormal = runIdentity . runNormalT
 
--type LiteralMap f = LiteralMapT f Identity
type LiteralMapT f = StateT (Int, Map.Map f Int)

--runLiteralMap :: LiteralMap p a -> a
--runLiteralMap action = runIdentity (runLiteralMapM action)

runLiteralMapM :: Monad m => LiteralMapT f m a -> m a
runLiteralMapM action = (runStateT action) (1, Map.empty) >>= return . fst

type SkolemT v term m = StateT (SkolemState v term) m

data SkolemState v term
    = SkolemState
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

newSkolemState :: SkolemState v term
newSkolemState = SkolemState { skolemCount = 1
                             , skolemMap = Map.empty
                             , univQuant = [] }

runSkolem :: SkolemT v term Identity a -> a
runSkolem = runIdentity . runSkolemT

runSkolemT :: Monad m => SkolemT v term m a -> m a
runSkolemT action = (runStateT action) newSkolemState >>= return . fst

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Eq formula) =>
                    formula -> SkolemT v term m formula
skolemNormalForm f = askolemize f >>= return . specialize . prenexNormalForm

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Eq formula) =>
              formula -> SkolemT v term m formula
askolemize = skolem . negationNormalForm {- nnf . simplify -}

-- |Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the SkolemT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> SkolemT v term m formula
skolem fm =
    foldFirstOrder qu co (\ _ -> return fm) (\ _ -> return fm) fm
    where
      qu Exists y p =
          do let xs = fv fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map vt (Set.toList xs))
             skolem (substituteEq y fx p)
      qu Forall x p = skolem p >>= return . for_all x
      co (BinOp l (:&:) r) = skolem2 (.&.) l r
      co (BinOp l (:|:) r) = skolem2 (.|.) l r
      co _ = return fm

skolem2 :: (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) =>
           (formula -> formula -> formula) -> formula -> formula -> SkolemT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

specialize :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> formula
specialize f =
    foldFirstOrder q (\ _ -> f) (\ _ -> f) (\ _ -> f) f
    where
      q Forall _ f' = specialize f'
      q _ _ _ = f

skolemize :: (Monad m, FirstOrderFormula fof atom v, AtomEq atom p term, Term term v f, Eq fof) => fof -> SkolemT v term m fof
-- skolemize fm = {- t1 $ -} specialize . pnf . askolemize $ fm
skolemize fm = askolemize fm >>= return . specialize . pnf

-- | Convert a first order formula into a disjunct of conjuncts of
-- literals.  Note that this can convert any instance of
-- FirstOrderFormula into any instance of Literal.
literal :: forall fof atom term v p f lit. (Literal fof atom v, Atom atom p term, Term term v f, Literal lit atom v, Ord lit) =>
           fof -> Set.Set (Set.Set lit)
literal fm =
    foldLiteral neg tf at fm
    where
      neg :: fof -> Set.Set (Set.Set lit)
      neg x = Set.map (Set.map (.~.)) (literal x)
      tf = Set.singleton . Set.singleton . fromBool
      at :: atom -> Set.Set (Set.Set lit)
      at x = foldAtom (\ _ _ -> Set.singleton (Set.singleton (Data.Logic.Classes.Literal.atomic x))) tf x
