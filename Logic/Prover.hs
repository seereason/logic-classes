{-# LANGUAGE RankNTypes #-}
module Logic.Prover 
    ( load
    , load'
    , tell
    , empty
    ) where

import Control.Monad.Identity (Identity, runIdentity)
import qualified Logic.Chiou.FirstOrderLogic as C
import qualified Logic.Chiou.KnowledgeBase as C
import qualified Logic.Chiou.Monad as C
import qualified Logic.Chiou.NormalForm as C
import Logic.FirstOrder (FirstOrderLogic(..), Skolem(..), Boolean(..), convertPred)
import Logic.Instances.Chiou ()
import Logic.Instances.Parameterized ()

load :: (FirstOrderLogic formula term v p f, Eq p, Eq f, Boolean p, Skolem f, Monad m) =>
          [formula] -> C.ProverT v p f m [(Maybe Bool, [formula])]
load xs = C.loadKB (map f2s xs) >>= return . map fromINF

load' :: (FirstOrderLogic formula term v p f, Eq p, Eq f, Boolean p, Skolem f) =>
         [formula] -> [(Maybe Bool, [formula])]
load' = runIdentity . C.runProverT . load

tell :: (FirstOrderLogic formula term v p f, Eq p, Eq f, Boolean p, Skolem f, Monad m) =>
        formula -> C.ProverT v p f m (Maybe Bool, [formula])
tell x = C.tellKB (f2s x) >>= return . fromINF

empty :: (FirstOrderLogic formula term v p f, Monad m) => C.ProverT v p f m ()
empty = C.emptyKB

{-
theorem :: (FirstOrderLogic formula term v p f, Eq p, Eq f, Boolean p, Skolem f) =>
           [formula] -> Maybe Bool
theorem = fromINF . map fst . runIdentity . C.runProverT . C.loadKB . map f2s
    -- If any of the results led to an invalid result, we couldn't insert all
    -- the sentences.  Otherwise, the final element the result.
    where fromINF xs = if any (== (Just False)) xs then Just False else last xs
-}

s2f :: (FirstOrderLogic formula term v p f, Skolem f) => C.Sentence v p f -> formula
s2f = convertPred id id id

f2s :: (FirstOrderLogic formula term v p f, Skolem f) => formula -> C.Sentence v p f
f2s = convertPred id id id

fromINF :: (FirstOrderLogic formula term v p f, Skolem f, Boolean p, Eq p) =>
           (t, [C.ImplicativeNormalForm v p f]) -> (t, [formula])
fromINF (flag, infs) = (flag, map (s2f . C.fromINF) infs)
