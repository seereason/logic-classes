{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeSynonymInstances #-}
-- |A monad to manage the knowledge base.
module Logic.Chiou.Monad
    ( SkolemCount
    , State(..)
    , FolModule
    , ProverT
    , zeroKB
    , runProverT
    ) where

import Control.Monad.State (MonadState, StateT, evalStateT, get, put)
import Logic.Chiou.NormalForm (ImplicativeNormalForm)

type SkolemCount = Int

data State v p f
    = State { knowledgeBase ::[(ImplicativeNormalForm v p f, SkolemCount)]
            , skolemCount :: SkolemCount
            , modules :: [FolModule] }

zeroKB :: State v p f
zeroKB = State { knowledgeBase = []
               , skolemCount = 0
               , modules = [("user", 0)] }

type FolModule = (String, SkolemCount)

-- |A monad for running the knowledge base.
type ProverT v p f = StateT (State v p f)

runProverT :: Monad m => StateT (State v p f) m a -> m a
runProverT action = evalStateT action zeroKB

class MonadState (State v p f) m => Skolem v p f m where
    skolem :: m Int

instance Monad m => Skolem v p f (ProverT v p f m) where
    skolem =
        get >>= \ st ->
        put (st {skolemCount = skolemCount st + 1}) >>
        return (skolemCount st) 
