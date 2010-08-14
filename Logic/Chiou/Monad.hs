{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeSynonymInstances #-}
-- |A monad to manage the knowledge base.
module Logic.Chiou.Monad
    ( WithId(..)
    , SentenceCount
    , withId
    , wiLookupItem
    , wiLookupId
    , KnowledgeBase
    , ProverState(..)
    , FolModule
    , ProverT
    , ProverT'
    , zeroKB
    , runProverT
    , runProverT'
    , runProver
    , runProver'
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT, evalStateT {-, MonadState, get, put-})
import Logic.Chiou.NormalForm (ImplicativeNormalForm)
import Logic.Monad (SkolemT, runSkolemT)

type SentenceCount = Int

data WithId a = WithId {wiItem :: a, wiIdent :: Int}

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

type KnowledgeBase v p f = [WithId (ImplicativeNormalForm v p f)]

data ProverState v p f
    = ProverState
      { knowledgeBase :: KnowledgeBase v p f
      , sentenceCount :: Int }

zeroKB :: ProverState v p f
zeroKB = ProverState
         { knowledgeBase = []
         , sentenceCount = 1 }

type FolModule = WithId String

-- |A monad for running the knowledge base.
type ProverT v p f = StateT (ProverState v p f)
type ProverT' term v p f m a = ProverT v p f (SkolemT v term m) a

runProverT' :: Monad m => ProverT' term v p f m a -> m a
runProverT' = runSkolemT . runProverT
runProverT :: Monad m => StateT (ProverState v p f) m a -> m a
runProverT action = evalStateT action zeroKB
runProver' :: ProverT' term v p f Identity a -> a
runProver' = runIdentity . runProverT'
runProver :: StateT (ProverState v p f) Identity a -> a
runProver = runIdentity . runProverT

{-
class MonadState (ProverState v p f) m => Skolem v p f m where
    skolem' :: m Int

instance Monad m => Skolem v p f (ProverT v p f m) where
    skolem' =
        get >>= \ st ->
        put (st {skolemCount = skolemCount' st + 1}) >>
        return (skolemCount st) 
-}
