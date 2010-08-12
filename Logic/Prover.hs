{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module Logic.Prover 
    ( load
    , load'
    , tell
    , empty
    ) where

import qualified Logic.Chiou.FirstOrderLogic as C
import qualified Logic.Chiou.KnowledgeBase as C
import qualified Logic.Chiou.Monad as C
import qualified Logic.Chiou.NormalForm as C
import Logic.FirstOrder (FirstOrderLogic(..), convertFOF)
import Logic.Implicative (Implicative, fromImplicative)
import Logic.Instances.Chiou ()
import Logic.Instances.Parameterized ()
import Logic.Monad (SkolemT, runSkolem)

load :: (FirstOrderLogic formula term v p f, Enum v, Ord p, Ord f, Monad m, Show v, Show p, Show f) =>
          [formula] -> C.ProverT v p f (SkolemT v (C.Term v f) m) [(Maybe Bool, [formula])]
load xs = C.loadKB (map f2s xs) >>= return . map fromINF'

load' :: (FirstOrderLogic formula term v p f, Enum v, Ord p, Ord f, Show v, Show p, Show f) =>
         [formula] -> [(Maybe Bool, [formula])]
load' = runSkolem . C.runProverT . load

-- |Try to add a sentence to the knowledge base.  The result value is
-- a pair, the Maybe Bool is
-- 
--  * Just True if the formula was proved using the existing knowledge base,
-- 
--  * Just False if it was disproven (i.e. its inverse was proven), and
-- 
--  * Nothing if it could neither be proven nor disproven.
-- 
-- The list of formulas is the proof or disproof or attempted proof
-- that was generated.  The new formula is added to the knowledge base
-- in all cases except for disproof.
tell :: (FirstOrderLogic formula term v p f, Enum v, Ord p, Ord f, Monad m, Show v, Show p, Show f) =>
        formula -> C.ProverT v p f (SkolemT v (C.Term v f) m) (Maybe Bool, [formula])
tell x = C.tellKB (f2s x) >>= return . fromINF'

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

s2f :: (FirstOrderLogic formula term v p f) => C.Sentence v p f -> formula
s2f = convertFOF id id id

f2s :: (FirstOrderLogic formula term v p f) => formula -> C.Sentence v p f
f2s = convertFOF id id id

fromINF' :: (FirstOrderLogic formula term v p f, Ord p, Ord f, Implicative (C.ImplicativeNormalForm v p f) (C.NormalSentence v p f)) =>
           (t, [C.ImplicativeNormalForm v p f]) -> (t, [formula])
fromINF' (flag, infs) = (flag, map (s2f . fromImplicative C.toSentence) infs)
