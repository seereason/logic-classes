{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror #-}

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
import Data.List (partition)
import Data.String (IsString)
import Logic.Chiou.FirstOrderLogic (Sentence(..))
import Logic.Chiou.Monad (ProverT, ProverState(..), zeroKB, SkolemCount, KnowledgeBase, FolModule)
import Logic.Chiou.NormalForm (ImplicativeNormalForm, toNormal)
import Logic.Chiou.Resolution (prove, SetOfSupport, getSetOfSupport)
import Logic.Chiou.Skolem (assignSkolemL)
import Logic.FirstOrder (Skolem(..))
import Logic.Logic (Boolean(..))
import Logic.Implicative (toImplicative)
import Logic.NormalForm (implicativeNormalForm)

-- |Reset the knowledgebase to empty.
emptyKB :: Monad m => ProverT v p f m ()
emptyKB = put zeroKB

unloadKB :: Monad m => String -> ProverT v p f m (Maybe (KnowledgeBase v p f))
unloadKB name =
    get >>= \ st -> maybe (return Nothing) (unload st) (lookup name (modules st))
    where
      unload st n =
          let (discard, keep) = partition ((== n) . snd) (knowledgeBase st) in
          put (st {knowledgeBase = keep}) >> return (Just discard)

-- |Return the contents of the knowledgebase.
getKB :: Monad m => ProverT v p f m [ImplicativeNormalForm v p f]
getKB = get >>= return . map fst . knowledgeBase

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m, Ord v, IsString v, Enum v, Boolean p, Ord p, Ord f, Skolem f, Show v, Show p, Show f) => Sentence v p f -> ProverT v p f m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
validKB :: (Monad m, Ord v, IsString v, Enum v, Ord p, Boolean p, Ord f, Skolem f, Show v, Show p, Show f) => Sentence v p f -> ProverT v p f m (Maybe Bool, SetOfSupport v p f, SetOfSupport v p f)
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB s >>= \ (disproved, proof2) ->
    return (if proved then Just True else if disproved then Just False else Nothing, proof1, proof2)

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
theoremKB :: (Monad m, Ord v, IsString v, Enum v, Ord p, Boolean p, Ord f, Skolem f, Show v, Show p, Show f) =>
             Sentence v p f -> ProverT v p f m (Bool, SetOfSupport v p f)
theoremKB s = inconsistantKB (Not s)

-- |Return a flag indicating whether sentence was disproved, along
-- with a disproof.
inconsistantKB :: (Monad m, Ord v, IsString v, Eq p, Enum v, Ord f, Skolem f, Ord p, Boolean p, Show v, Show p, Show f) =>
                  Sentence v p f -> ProverT v p f m (Bool, SetOfSupport v p f)
inconsistantKB s = getKB >>= return . prove [] (getSetOfSupport (toImplicative toNormal (implicativeNormalForm s)))

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (Monad m, Ord v, IsString v, Enum v, Ord p, Boolean p, Ord f, Skolem f, Show v, Show p, Show f) =>
          Sentence v p f -> ProverT v p f m (Maybe Bool, [ImplicativeNormalForm v p f])
tellKB s = do (inf, sc) <-  assignSkolemL (toImplicative toNormal (implicativeNormalForm s)) 0
              (valid, _, _) <- validKB s
              case valid of
                Just False -> return ()
                _ -> modify (\ st -> st { knowledgeBase = knowledgeBase st ++ inf
                                        , skolemCount = skolemCount st + sc })
              return (valid, map fst inf)

loadKB :: (Monad m, Ord v, IsString v, Enum v, Ord p, Boolean p, Ord f, Skolem f, Show v, Show p, Show f) =>
          [Sentence v p f] -> ProverT v p f m [(Maybe Bool, [ImplicativeNormalForm v p f])]
loadKB sentences = emptyKB >> mapM tellKB sentences

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
showKB = get >>= return . reportKB 1

reportKB :: (Show (ImplicativeNormalForm v p f), Show v, Show p, Show f) => SkolemCount -> ProverState v p f -> String
reportKB _ (ProverState {knowledgeBase = []}) = "Nothing in Knowledge Base\n"
reportKB i (ProverState {knowledgeBase = [x], modules = m}) =
    show i ++ ") " ++ reportKB' (snd x) m ++ "\t" ++ show (fst x) ++ "\n"
reportKB i st@(ProverState {knowledgeBase = (x:xs), modules = m}) =
    show i ++ ") " ++ reportKB' (snd x) m ++  "\t" ++ show (fst x) ++ "\n" ++ reportKB (i + 1) (st {knowledgeBase = xs})

reportKB' :: SkolemCount -> [FolModule] -> String
reportKB' 0 _m = "[USER]"
reportKB' i m =
    case lookup i (map (\(a, b) -> (b, a)) m) of
      Just x -> "[MOD:" ++ x ++ "]"
      Nothing -> "ERROR"
