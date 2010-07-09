{-# LANGUAGE RankNTypes #-}
module Logic.Prover 
    ( loadKB
    , theorem
    ) where

import Control.Monad.Identity (Identity, runIdentity)
import Data.String (IsString(..))
import qualified Logic.Chiou.FirstOrderLogic as C
import qualified Logic.Chiou.KnowledgeBase as C
import qualified Logic.Chiou.Monad as C
import qualified Logic.Chiou.NormalForm as C
import Logic.FirstOrder (FirstOrderLogic(..), Skolem(..), convertPred)
import Logic.Instances.Chiou ()
import Logic.Instances.Parameterized ()

loadKB :: forall formula term v p f.
          (FirstOrderLogic formula term v p f, Eq p, Eq f, IsString p, Skolem f) =>
          [formula] -> [(Maybe Bool, [formula])]
loadKB xs =
    map fromINF (runIdentity (C.runProverT (C.loadKB (map f2s xs))))
    where fromINF (flag, infs) = (flag, map (s2f . C.fromINF) infs)

theorem :: forall formula term v p f.
           (FirstOrderLogic formula term v p f, Eq p, Eq f, IsString p, Skolem f) =>
           [formula] -> Maybe Bool
    fromINF . map fst $ (runIdentity (C.runProverT (C.loadKB (map f2s xs))))
    -- If any of the results led to an invalid result, we couldn't insert all
    -- the sentences.  Otherwise, the final element the result.
    where fromINF xs = if any (== (Just False)) xs then Just False else last xs

s2f :: (FirstOrderLogic formula term v p f, Skolem f) => C.Sentence v p f -> formula
s2f = convertPred id id id

f2s :: (FirstOrderLogic formula term v p f, Skolem f) => formula -> C.Sentence v p f
f2s = convertPred id id id
