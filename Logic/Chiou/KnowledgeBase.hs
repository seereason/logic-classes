{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Wwarn #-}

{- KnowledgeBase.hs -}
{- Charles Chiou, David Fox -}

module Logic.Chiou.KnowledgeBase
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
import Data.String (IsString)
import qualified Logic.Chiou.FirstOrderLogic as C
import Logic.Chiou.FirstOrderLogic (Sentence(..))
import Logic.Chiou.Monad (ProverT, ProverT', ProverState(..), KnowledgeBase, WithId(..), SentenceCount, withId, zeroKB)
import Logic.Chiou.NormalForm (ImplicativeNormalForm, fromSentence, NormalSentence, NormalTerm)
import Logic.FirstOrder (Skolem(..), Pretty, Term)
import Logic.Implicative (toImplicative)
import Logic.Logic (Boolean(..), Logic)
import Logic.NormalForm (implicativeNormalForm)
import Logic.Resolution (prove, getSetOfSupport)

-- |Reset the knowledgebase to empty.
emptyKB :: Monad m => ProverT v p f m ()
emptyKB = put zeroKB

-- |Remove a particular sentence from the knowledge base
unloadKB :: Monad m => SentenceCount -> ProverT v p f m (Maybe (KnowledgeBase v p f))
unloadKB n =
    do st <- get
       let (discard, keep) = partition ((== n) . wiIdent) (knowledgeBase st)
       put (st {knowledgeBase = keep}) >> return (Just discard)

-- |Return the contents of the knowledgebase.
getKB :: Monad m => ProverT v p f m [WithId (ImplicativeNormalForm v p f)]
getKB = get >>= return . knowledgeBase

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m, Ord v, IsString v, Enum v, Data v, Boolean p, Ord p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
         Sentence v p f -> ProverT' (C.Term v f) v p f m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
{-
validKB :: (Monad m, Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
           Sentence v p f -> ProverT' (C.Term v f) v p f m (Maybe Bool, SetOfSupport v p f, SetOfSupport v p f)
-}
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB s >>= \ (disproved, proof2) ->
    return (if proved then Just True else if disproved then Just False else Nothing, proof1, proof2)

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
{-
theoremKB :: (Monad m, Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
             Sentence v p f -> ProverT' (C.Term v f) v p f m (Bool, SetOfSupport v p f)
-}
theoremKB s = inconsistantKB (Not s)

-- |Return a flag indicating whether sentence was disproved, along
-- with a disproof.
{-
inconsistantKB :: (Monad m, Ord v, Data v, Enum v, Ord p, Data p, Boolean p, Ord f, Data f, Skolem f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
                  Sentence v p f -> ProverT' (C.Term v f) v p f m (Bool, SetOfSupport v p f)
-}
inconsistantKB s = lift (implicativeNormalForm s) >>= \ inf -> getKB >>= return . prove [] (getSetOfSupport (toImplicative fromSentence inf)) . map wiItem

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (Monad m, Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
          Sentence v p f -> ProverT' (C.Term v f) v p f m (Maybe Bool, [ImplicativeNormalForm v p f])
tellKB s =
    do st <- get
       inf <- lift (implicativeNormalForm s)
       -- (inf', sc) <- assignSkolemL (toImplicative toNormal inf)
       let inf' = map (withId (sentenceCount st)) (toImplicative fromSentence inf)
       (valid, _, _) <- validKB s
       case valid of
         Just False -> return ()
         _ -> put st { knowledgeBase = knowledgeBase st ++ inf'
                     , sentenceCount = sentenceCount st + 1 }
       return (valid, map wiItem inf')

loadKB :: (Monad m, Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f, Term (NormalTerm v f) v f, Logic (NormalSentence v p f)) =>
          [Sentence v p f] -> ProverT' (C.Term v f) v p f m [(Maybe Bool, [ImplicativeNormalForm v p f])]
loadKB sentences = mapM tellKB sentences

-- |Delete an entry from the KB.
deleteKB :: Monad m => Int -> ProverT v p f m String
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
showKB :: (Show (ImplicativeNormalForm v p f), Monad m, Show v, Show p, Show f) => ProverT v p f m String
showKB = get >>= return . reportKB

reportKB :: (Show (ImplicativeNormalForm v p f), Show v, Show p, Show f) => ProverState v p f -> String
reportKB (ProverState {knowledgeBase = []}) = "Nothing in Knowledge Base\n"
reportKB (ProverState {knowledgeBase = [WithId {wiItem = x, wiIdent = n}]}) =
    show n ++ ") " ++ "\t" ++ show x ++ "\n"
reportKB st@(ProverState {knowledgeBase = (WithId {wiItem = x, wiIdent = n}:xs)}) =
    show n ++ ") " ++ "\t" ++ show x ++ "\n" ++ reportKB (st {knowledgeBase = xs})
