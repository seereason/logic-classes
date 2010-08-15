{-# LANGUAGE DeriveDataTypeable #-}
module Logic.Monad
    ( LogicState(..)
    , newLogicState
    , SkolemT
    , runSkolemT
    , runSkolem
    , LiteralMap
    , LiteralMapT
    , runLiteralMap
    , runLiteralMapM
    , WithId(..)
    , SentenceCount
    , withId
    , wiLookupItem
    , wiLookupId
    , KnowledgeBase
    , ProverState(..)
    , ProverT
    , ProverT'
    , zeroKB
    , runProverT
    , runProverT'
    , runProver
    , runProver'
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT(runStateT), evalStateT)
import Data.Generics (Data, Typeable)
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

type SentenceCount = Int

data WithId a = WithId {wiItem :: a, wiIdent :: Int} deriving (Eq, Show, Data, Typeable)

withId :: Int -> a -> WithId a
withId i x = WithId {wiIdent = i, wiItem = x}

withIdPairs :: [WithId a] -> [(a, Int)]
withIdPairs = map (\ x -> (wiItem x, wiIdent x))

wiLookupId :: Eq a => a -> [WithId a] -> Maybe Int
wiLookupId x xs = lookup x (withIdPairs xs)

withIdPairs' :: [WithId a] -> [(Int, a)]
withIdPairs' = map (\ x -> (wiIdent x, wiItem x))

wiLookupItem :: Int -> [WithId a] -> Maybe a
wiLookupItem i xs = lookup i (withIdPairs' xs)

type KnowledgeBase inf = [WithId inf]

data ProverState inf
    = ProverState
      { knowledgeBase :: KnowledgeBase inf
      , sentenceCount :: Int }

zeroKB :: ProverState inf
zeroKB = ProverState
         { knowledgeBase = []
         , sentenceCount = 1 }

-- |A monad for running the knowledge base.
type ProverT inf = StateT (ProverState inf)
type ProverT' v term inf m a = ProverT inf (SkolemT v term m) a

runProverT' :: Monad m => ProverT' v term inf m a -> m a
runProverT' = runSkolemT . runProverT
runProverT :: Monad m => StateT (ProverState inf) m a -> m a
runProverT action = evalStateT action zeroKB
runProver' :: ProverT' v term inf Identity a -> a
runProver' = runIdentity . runProverT'
runProver :: StateT (ProverState inf) Identity a -> a
runProver = runIdentity . runProverT
