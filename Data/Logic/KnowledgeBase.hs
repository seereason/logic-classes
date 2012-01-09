{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, PackageImports,
             RankNTypes, TemplateHaskell, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall #-}

{- KnowledgeBase.hs -}
{- Charles Chiou, David Fox -}

module Data.Logic.KnowledgeBase
    ( WithId(WithId, wiItem, wiIdent) -- Probably only used by some unit tests, and not really correctly
    , ProverT
    , runProver'
    , runProverT'
    , getKB
    , unloadKB
    -- , deleteKB
    , askKB
    , theoremKB
    , inconsistantKB
    , ProofResult(Proved, Disproved, Invalid)
    , Proof(Proof, proofResult, proof)
    , validKB
    , tellKB
    , loadKB
    , showKB
    ) where

import "mtl" Control.Monad.Identity (Identity(runIdentity))
import "mtl" Control.Monad.State (StateT, evalStateT, MonadState(get, put))
import "mtl" Control.Monad.Trans (lift)
import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Constants (Constants)
import Data.Logic.Classes.Equals (AtomEq, varAtomEq, substAtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula)
import Data.Logic.Classes.Formula (Formula)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Term (Term)
import Data.Logic.Harrison.Skolem (SkolemT, runSkolemT)
import Data.Logic.Normal.Implicative (ImplicativeForm, implicativeNormalForm)
import Data.Logic.Resolution (prove, SetOfSupport, getSetOfSupport)
import Data.SafeCopy (deriveSafeCopy, base)
import qualified Data.Set.Extra as S
import Happstack.Data (Default(defaultValue), deriveNewDataNoDefault)
import Prelude hiding (negate)

type SentenceCount = Int

data WithId a = WithId {wiItem :: a, wiIdent :: Int} deriving (Eq, Ord, Show, Data, Typeable)

withId :: Int -> a -> WithId a
withId i x = WithId {wiIdent = i, wiItem = x}

{-
withIdPairs :: [WithId a] -> [(a, Int)]
withIdPairs = map (\ x -> (wiItem x, wiIdent x))

wiLookupId :: Eq a => a -> [WithId a] -> Maybe Int
wiLookupId x xs = lookup x (withIdPairs xs)

withIdPairs' :: [WithId a] -> [(Int, a)]
withIdPairs' = map (\ x -> (wiIdent x, wiItem x))

wiLookupItem :: Int -> [WithId a] -> Maybe a
wiLookupItem i xs = lookup i (withIdPairs' xs)
-}

type KnowledgeBase inf = S.Set (WithId inf)

data ProverState inf
    = ProverState
      { recursionLimit :: Maybe Int
      , knowledgeBase :: KnowledgeBase inf
      , sentenceCount :: Int }

zeroKB :: Maybe Int -> ProverState inf
zeroKB limit =
    ProverState
         { recursionLimit = limit
         , knowledgeBase = S.empty
         , sentenceCount = 1 }

-- |A monad for running the knowledge base.
type ProverT inf = StateT (ProverState inf)
type ProverT' v term inf m a = ProverT inf (SkolemT v term m) a

runProverT' :: Monad m => Maybe Int -> ProverT' v term inf m a -> m a
runProverT' limit = runSkolemT . runProverT limit
runProverT :: Monad m => Maybe Int -> StateT (ProverState inf) m a -> m a
runProverT limit action = evalStateT action (zeroKB limit)
runProver' :: Maybe Int -> ProverT' v term inf Identity a -> a
runProver' limit = runIdentity . runProverT' limit
{-
runProver :: StateT (ProverState inf) Identity a -> a
runProver = runIdentity . runProverT
-}

data ProofResult
    = Disproved
    -- ^ The conjecture is unsatisfiable
    | Proved
    -- ^ The negated conjecture is unsatisfiable
    | Invalid
    -- ^ Both are satisfiable
    deriving (Data, Typeable, Eq, Ord, Show)

$(deriveSafeCopy 1 'base ''ProofResult)

$(deriveNewDataNoDefault [''ProofResult])

instance Default ProofResult where
    defaultValue = Invalid

data Proof lit = Proof {proofResult :: ProofResult, proof :: S.Set (ImplicativeForm lit)} deriving (Data, Typeable, Eq, Ord)

instance (Ord lit, Show lit, Literal lit atom v, FirstOrderFormula lit atom v) => Show (Proof lit) where
    show p = "Proof {proofResult = " ++ show (proofResult p) ++ ", proof = " ++ show (proof p) ++ "}"

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
inconsistantKB :: forall m formula atom term v p f lit.
                  (FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
                   Monad m, Show term, Eq formula, Data formula, Data lit, Eq lit, Ord lit, Ord term, Constants p, Eq p) =>
                  formula -> ProverT' v term (ImplicativeForm lit) m (Bool, SetOfSupport lit v term)
inconsistantKB s =
    get >>= \ st ->
    lift (implicativeNormalForm varAtomEq substAtomEq s) >>=
    return . getSetOfSupport >>= \ sos ->
    getKB >>=
    return . prove (recursionLimit st) S.empty sos . S.map wiItem

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
theoremKB :: forall m formula atom term v p f lit.
             (Monad m, FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
              Show term, Eq formula, Ord term, Ord lit, Data formula, Data lit, Constants p, Eq p) =>
             formula -> ProverT' v term (ImplicativeForm lit) m (Bool, SetOfSupport lit v term)
theoremKB s = inconsistantKB ((.~.) s)

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m, FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
          Eq formula, Show term, Ord term, Ord lit, Data formula, Data lit, Constants p, Eq p) =>
         formula -> ProverT' v term (ImplicativeForm lit) m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
validKB :: (FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
            Monad m, Eq formula, Show term, Ord term, Ord lit, Data formula, Data lit, Constants p, Eq p) =>
           formula -> ProverT' v term (ImplicativeForm lit) m (ProofResult, SetOfSupport lit v term, SetOfSupport lit v term)
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB s >>= \ (disproved, proof2) ->
    return (if proved then Proved else if disproved then Disproved else Invalid, proof1, proof2)

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
           Monad m, Show term, Eq formula, Data formula, Data lit, Eq lit, Ord lit, Ord term, Constants p, Eq p) =>
          formula -> ProverT' v term (ImplicativeForm lit) m (Proof lit)
tellKB s =
    do st <- get
       inf <- lift (implicativeNormalForm varAtomEq substAtomEq s)
       let inf' = S.map (withId (sentenceCount st)) inf
       (valid, _, _) <- validKB s
       case valid of
         Disproved -> return ()
         _ -> put st { knowledgeBase = S.union (knowledgeBase st) inf'
                     , sentenceCount = sentenceCount st + 1 }
       return $ Proof {proofResult = valid, proof = S.map wiItem inf'}

loadKB :: (FirstOrderFormula formula atom v, Literal lit atom v, Formula atom term v, AtomEq atom p term, Term term v f,
           Monad m, Eq formula, Show term, Ord term, Ord lit, Data formula, Data lit, Constants p, Eq p) =>
          [formula] -> ProverT' v term (ImplicativeForm lit) m [Proof lit]
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
