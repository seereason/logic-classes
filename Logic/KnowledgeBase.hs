{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Wwarn #-}

{- KnowledgeBase.hs -}
{- Charles Chiou, David Fox -}

module Logic.KnowledgeBase
    ( getKB
    , emptyKB
    , unloadKB
    -- , deleteKB
    , askKB
    , theoremKB
    , inconsistantKB
    , ProofResult(..)
    , validKB
    , tellKB
    , loadKB
    , showKB
    ) where

import Control.Monad.State (MonadState(get, put))
import Control.Monad.Trans (lift)
import Data.Generics (Data, Typeable)
import Logic.FirstOrder (FirstOrderFormula)
import Logic.Logic (Negatable(..))
import Logic.Monad (ProverT, ProverT', ProverState(..), KnowledgeBase, WithId(..), SentenceCount, withId, zeroKB)
import Logic.Normal (ImplicativeNormalForm, Literal)
import Logic.NormalForm (implicativeNormalForm)
import Logic.Resolution (prove, SetOfSupport, getSetOfSupport)
import qualified Logic.Set as S
import Prelude hiding (negate)

data ProofResult
    = Disproved
    -- ^ The conjecture is unsatisfiable
    | Proved
    -- ^ The negated conjecture is unsatisfiable
    | Invalid
    -- ^ Both are satisfiable
    deriving (Data, Typeable, Eq, Show)
-- |Reset the knowledgebase to empty.
emptyKB :: Monad m => ProverT inf m ()
emptyKB = put zeroKB

-- |Remove a particular sentence from the knowledge base
unloadKB :: (Monad m, Ord inf) => SentenceCount -> ProverT inf m (Maybe (KnowledgeBase inf))
unloadKB n =
    do st <- get
       let (discard, keep) = S.partition ((== n) . wiIdent) (knowledgeBase st)
       put (st {knowledgeBase = keep}) >> return (Just discard)

-- |Return the contents of the knowledgebase.
getKB :: Monad m => ProverT inf m (S.Set (WithId inf))
getKB = get >>= return . knowledgeBase

-- |Return a flag indicating whether sentence was disproved, along
-- with a disproof.
inconsistantKB :: forall m formula term v p f lit p1 f1 v1 term1.
                  (FirstOrderFormula formula term v p f, Literal lit term1 v1 p1 f1, Monad m) =>
                 (v -> v1) -> (p -> p1) -> (f -> f1) -> formula -> ProverT' v term (ImplicativeNormalForm lit) m (Bool, SetOfSupport lit v1 term1)
inconsistantKB cv cp cf s = lift (implicativeNormalForm cv cp cf s) >>= return . getSetOfSupport >>= \ sos -> getKB >>= return . prove S.empty sos . S.map wiItem

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
theoremKB :: (Monad m, FirstOrderFormula formula term v p f, Literal formula term v p f) =>
             formula -> ProverT' v term (ImplicativeNormalForm formula) m (Bool, SetOfSupport formula v term)
theoremKB s = inconsistantKB id id id ((.~.) s)

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m, FirstOrderFormula formula term v p f, Literal formula term v p f) =>
         formula -> ProverT' v term (ImplicativeNormalForm formula) m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
validKB :: (FirstOrderFormula formula term v p f, Literal formula term v p f, Monad m) =>
           formula -> ProverT' v term (ImplicativeNormalForm formula) m (ProofResult, SetOfSupport formula v term, SetOfSupport formula v term)
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB id id id s >>= \ (disproved, proof2) ->
    return (if proved then Proved else if disproved then Disproved else Invalid, proof1, proof2)

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (FirstOrderFormula formula term v p f, Literal formula term v p f, Monad m) =>
          formula -> ProverT' v term (ImplicativeNormalForm formula) m (ProofResult, S.Set (ImplicativeNormalForm formula))
tellKB s =
    do st <- get
       inf <- lift (implicativeNormalForm id id id s)
       let inf' = S.map (withId (sentenceCount st)) inf
       (valid, _, _) <- validKB s
       case valid of
         Disproved -> return ()
         _ -> put st { knowledgeBase = S.union (knowledgeBase st) inf'
                     , sentenceCount = sentenceCount st + 1 }
       return (valid, S.map wiItem inf')

loadKB :: (FirstOrderFormula formula term v p f, Literal formula term v p f, Monad m) =>
          [formula] -> ProverT' v term (ImplicativeNormalForm formula) m [(ProofResult, S.Set (ImplicativeNormalForm formula))]
loadKB sentences = mapM tellKB sentences

-- |Delete an entry from the KB.
{-
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
-}

-- |Return a text description of the contents of the knowledgebase.
showKB :: (Show inf, Monad m) => ProverT inf m String
showKB = get >>= return . reportKB

reportKB :: (Show inf) => ProverState inf -> String
reportKB st@(ProverState {knowledgeBase = kb}) =
    case S.minView kb of
      Nothing -> "Nothing in Knowledge Base\n"
      Just (WithId {wiItem = x, wiIdent = n}, kb')
          | S.null kb' ->
              show n ++ ") " ++ "\t" ++ show x ++ "\n"
          | True ->
              show n ++ ") " ++ "\t" ++ show x ++ "\n" ++ reportKB (st {knowledgeBase = kb'})
