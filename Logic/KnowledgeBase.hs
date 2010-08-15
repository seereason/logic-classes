{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Wwarn #-}

{- KnowledgeBase.hs -}
{- Charles Chiou, David Fox -}

module Logic.KnowledgeBase
    ( getKB
    , emptyKB
    , unloadKB
    , deleteKB
    , askKB
    , theoremKB
    , inconsistantKB
    , validKB
    , tellKB
    , loadKB
    , showKB
    ) where

import Control.Monad.State (MonadState(get, put), modify)
import Control.Monad.Trans (lift)
import Data.Generics (Data)
import Data.List (partition)
import Logic.Clause (Literal(..))
import Logic.FirstOrder (FirstOrderLogic)
import Logic.Implicative (Implicative, toImplicative)
import Logic.Monad (ProverT, ProverT', ProverState(..), KnowledgeBase, WithId(..), SentenceCount, withId, zeroKB)
import Logic.NormalForm (implicativeNormalForm)
import Logic.Resolution (prove, SetOfSupport, getSetOfSupport)
import Prelude hiding (negate)

-- |Reset the knowledgebase to empty.
emptyKB :: Monad m => ProverT inf m ()
emptyKB = put zeroKB

-- |Remove a particular sentence from the knowledge base
unloadKB :: Monad m => SentenceCount -> ProverT inf m (Maybe (KnowledgeBase inf))
unloadKB n =
    do st <- get
       let (discard, keep) = partition ((== n) . wiIdent) (knowledgeBase st)
       put (st {knowledgeBase = keep}) >> return (Just discard)

-- |Return the contents of the knowledgebase.
getKB :: Monad m => ProverT inf m [WithId inf]
getKB = get >>= return . knowledgeBase

-- |Return a flag indicating whether sentence was disproved, along
-- with a disproof.
inconsistantKB :: (Monad m, FirstOrderLogic formula term v p f, Data formula, Implicative inf formula, Eq term) => formula -> ProverT' v term inf m (Bool, SetOfSupport inf v term)
inconsistantKB s = lift (implicativeNormalForm s) >>= return . getSetOfSupport . toImplicative id >>= \ sos -> getKB >>= return . prove [] sos . map wiItem

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
theoremKB :: (Monad m, FirstOrderLogic formula term v p f, Data formula, Implicative inf formula, Eq term) =>
             formula -> ProverT' v term inf m (Bool, SetOfSupport inf v term)
theoremKB s = inconsistantKB (negate s)

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m, FirstOrderLogic formula term v p f, Data formula, Implicative inf formula, Eq term) =>
         formula -> ProverT' v term inf m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
--validKB :: (Implicative inf (NormalSentence v p f), Pretty f, Skolem f, Eq f, Ord v, Enum v, Data v, Data f, Eq p, Boolean p, Data p, Pretty p, Pretty v, Monad m) =>
--           Sentence v p f -> ProverT' v (C.CTerm v f) inf m (Maybe Bool, SetOfSupport inf v (NormalTerm v f), SetOfSupport inf v (NormalTerm v f))
validKB :: (FirstOrderLogic formula term v p f, Eq term, Implicative inf formula, Data formula, Monad m) =>
           formula -> ProverT' v term inf m (Maybe Bool, SetOfSupport inf v term, SetOfSupport inf v term)
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB s >>= \ (disproved, proof2) ->
    return (if proved then Just True else if disproved then Just False else Nothing, proof1, proof2)

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (FirstOrderLogic formula term v p f, Implicative inf formula, Data formula, Eq term, Monad m) =>
          formula -> ProverT' v term inf m (Maybe Bool, [inf])
tellKB s =
    do st <- get
       inf <- lift (implicativeNormalForm s) >>= return . toImplicative id
       let inf' = map (withId (sentenceCount st)) inf
       (valid, _, _) <- validKB s
       case valid of
         Just False -> return ()
         _ -> put st { knowledgeBase = knowledgeBase st ++ inf'
                     , sentenceCount = sentenceCount st + 1 }
       return (valid, map wiItem inf')

loadKB :: (FirstOrderLogic formula term v p f, Implicative inf formula, Eq term, Data formula, Monad m) =>
          [formula] -> ProverT' v term inf m [(Maybe Bool, [inf])]
loadKB sentences = mapM tellKB sentences

-- |Delete an entry from the KB.
deleteKB :: Monad m => Int -> ProverT inf m String
deleteKB i = do st <- get
                modify (\ st' -> st' {knowledgeBase = deleteElement i (knowledgeBase st')})
                st' <- get
		return (if length (knowledgeBase st') /= length (knowledgeBase st) then
			  "Deleted"
			else
			  "Failed to delete")
	     
deleteElement :: Int -> [a] -> [a]
deleteElement i l
    | i <= 0    = l
    | otherwise = let
		    (p1, p2) = splitAt (i - 1) l
		  in
		    p1 ++ (case p2 of
			       [] -> []
			       _ -> tail p2)

-- |Return a text description of the contents of the knowledgebase.
showKB :: (Show inf, Monad m) => ProverT inf m String
showKB = get >>= return . reportKB

reportKB :: (Show inf) => ProverState inf -> String
reportKB (ProverState {knowledgeBase = []}) = "Nothing in Knowledge Base\n"
reportKB (ProverState {knowledgeBase = [WithId {wiItem = x, wiIdent = n}]}) =
    show n ++ ") " ++ "\t" ++ show x ++ "\n"
reportKB st@(ProverState {knowledgeBase = (WithId {wiItem = x, wiIdent = n}:xs)}) =
    show n ++ ") " ++ "\t" ++ show x ++ "\n" ++ reportKB (st {knowledgeBase = xs})
