{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
-- |A monad to manage the knowledge base.
module Logic.Chiou.Monad
    ( SkolemCount
    , KnowledgeBase
    , ProverState(..)
    , FolModule
    , ProverT
    , zeroKB
    , runProverT
    ) where

import Control.Monad.State (MonadState, StateT, evalStateT, get, put)
import Logic.Chiou.NormalForm (ImplicativeNormalForm)

type SkolemCount = Int

type KnowledgeBase v p f = [(ImplicativeNormalForm v p f, SkolemCount)]

data ProverState v p f
    = ProverState
      { knowledgeBase :: KnowledgeBase v p f
      , skolemCount :: SkolemCount
      , modules :: [FolModule] }

zeroKB :: ProverState v p f
zeroKB = ProverState
         { knowledgeBase = []
         , skolemCount = 0
         , modules = [("user", 0)] }

type FolModule = (String, SkolemCount)

-- |A monad for running the knowledge base.
type ProverT v p f = StateT (ProverState v p f)

runProverT :: Monad m => StateT (ProverState v p f) m a -> m a
runProverT action = evalStateT action zeroKB

class MonadState (ProverState v p f) m => Skolem v p f m where
    skolem :: m Int

instance Monad m => Skolem v p f (ProverT v p f m) where
    skolem =
        get >>= \ st ->
        put (st {skolemCount = skolemCount st + 1}) >>
        return (skolemCount st) 
