module Logic.Monad
    ( LogicState(..)
    , SkolemT
    , runSkolemT
    , runSkolem
    , LiteralMap
    , LiteralMapT
    , runLiteralMap
    , runLiteralMapM
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT(runStateT))
import qualified Data.Map as Map

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

type SkolemT v term m = StateT (LogicState v term) m

runSkolemT :: Monad m => SkolemT v term m a -> m a
-- runSkolemT :: (Monad m, FirstOrderLogic formula term v p f) => m a -> SkolemT v term m a
runSkolemT action = (runStateT action) newLogicState >>= return . fst
runSkolem :: SkolemT v term Identity a -> a
runSkolem = runIdentity . runSkolemT
 
-- |A Monad for creating and maintaining a map from literals of type p
-- to literals of type Int.
type LiteralMap f = LiteralMapT f Identity
type LiteralMapT f = StateT (Int, Map.Map f Int)

runLiteralMap :: LiteralMap p a -> a
runLiteralMap action = runIdentity (runLiteralMapM action)
runLiteralMapM :: Monad m => LiteralMapT f m a -> m a
runLiteralMapM action = (runStateT action) (1, Map.empty) >>= return . fst
