{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, PackageImports,
             RankNTypes, TemplateHaskell, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall #-}

{- KnowledgeBase.hs -}
{- Charles Chiou, David Fox -}

module Data.Logic.KnowledgeBase
    ( WithId(WithId, wiItem, wiIdent) -- Probably only used by some unit tests, and not really correctly
    , ProverT, ProverT'
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
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Normal.Implicative (ImplicativeForm, implicativeNormalForm, prettyProof)
import Data.Logic.Resolution (prove, SetOfSupport, getSetOfSupport)
import Data.SafeCopy (deriveSafeCopy, base)
import Data.Set.Extra as Set (Set, empty, map, minView, null, partition, union)
import FOL (HasApply(TermOf, PredOf), HasApplyAndEquate, IsFirstOrder, IsFunction, IsQuantified(VarOf), IsTerm(FunOf))
import Formulas ((.~.), IsFormula(AtomOf))
import Lib (Marked)
import Lit (IsLiteral, Literal)
import Prelude hiding (negate)
import Pretty (Pretty(pPrint), text, (<>))
import Skolem (SkolemT, runSkolemT, HasSkolem(SVarOf))

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

type KnowledgeBase inf = Set (WithId inf)

data ProverState inf
    = ProverState
      { recursionLimit :: Maybe Int
      , knowledgeBase :: KnowledgeBase inf
      , sentenceCount :: Int }

zeroKB :: Maybe Int -> ProverState inf
zeroKB limit =
    ProverState
         { recursionLimit = limit
         , knowledgeBase = Set.empty
         , sentenceCount = 1 }

-- |A monad for running the knowledge base.
type ProverT inf = StateT (ProverState inf)
type ProverT' v term lit m a = ProverT (ImplicativeForm lit) (SkolemT m (FunOf term)) a

runProverT' :: (Monad m, IsFunction (FunOf term), term ~ TermOf atom, atom ~ AtomOf lit) => Maybe Int -> ProverT' v term lit m a -> m a
runProverT' limit = runSkolemT . runProverT limit
runProverT :: Monad m => Maybe Int -> StateT (ProverState inf) m a -> m a
runProverT limit action = evalStateT action (zeroKB limit)
runProver' :: (IsFunction (FunOf term), term ~ TermOf atom, atom ~ AtomOf lit) => Maybe Int -> ProverT' v term lit Identity a -> a
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

instance Pretty ProofResult where
    pPrint = text . show

$(deriveSafeCopy 1 'base ''ProofResult)

data Proof lit = Proof {proofResult :: ProofResult, proof :: Set (ImplicativeForm lit)} deriving (Data, Typeable, Eq, Ord)

instance (Ord lit, Show lit, IsLiteral lit) => Show (Proof lit) where
    show p = "Proof {proofResult = " ++ show (proofResult p) ++ ", proof = " ++ show (proof p) ++ "}"

instance (Ord lit, Pretty lit, Show lit, IsLiteral lit) => Pretty (Proof lit) where
    pPrint p = text "Proof {\n  proofResult = " <> pPrint (proofResult p) <> text ",\n  proof = " <> prettyProof (proof p) <> text "\n}"

-- |Remove a particular sentence from the knowledge base
unloadKB :: (Monad m, Ord inf) => SentenceCount -> ProverT inf m (Maybe (KnowledgeBase inf))
unloadKB n =
    do st <- get
       let (discard, keep) = Set.partition ((== n) . wiIdent) (knowledgeBase st)
       put (st {knowledgeBase = keep}) >> return (Just discard)

-- |Return the contents of the knowledgebase.
getKB :: Monad m => ProverT inf m (Set (WithId inf))
getKB = get >>= return . knowledgeBase

-- |Return a flag indicating whether sentence was disproved, along
-- with a disproof.
inconsistantKB :: forall m fof lit atom term v function.
                  (IsFirstOrder fof,
                   Ord fof, lit ~ Marked Literal fof,
                   Atom atom term v,
                   HasApplyAndEquate atom,
                   IsTerm term,
                   HasSkolem function,
                   Monad m, Data fof, Pretty fof, Typeable function,
                   atom ~ AtomOf fof, term ~ TermOf atom,
                   function ~ FunOf term,
                   v ~ VarOf fof, v ~ SVarOf function) =>
                  fof -> ProverT' v term lit m (Bool, SetOfSupport lit v term)
inconsistantKB s =
    get >>= \ st ->
    lift (implicativeNormalForm s) >>=
    return . getSetOfSupport >>= \ sos ->
    getKB >>=
    return . prove (recursionLimit st) Set.empty sos . Set.map wiItem

-- |Return a flag indicating whether sentence was proved, along with a
-- proof.
theoremKB :: forall m fof lit atom term v function.
             (Monad m,
              IsFirstOrder fof, Ord fof, Pretty fof, lit ~ Marked Literal fof,
              Atom atom term v,
              HasApplyAndEquate atom,
              IsTerm term,
              HasSkolem function,
              Data fof, Typeable function,
              atom ~ AtomOf fof, term ~ TermOf atom,
              function ~ FunOf term,
              v ~ VarOf fof, v ~ SVarOf function) =>
             fof -> ProverT' v term lit m (Bool, SetOfSupport lit v term)
theoremKB s = inconsistantKB ((.~.) s)

-- |Try to prove a sentence, return the result and the proof.
-- askKB should be in KnowledgeBase module. However, since resolution
-- is here functions are here, it is also placed in this module.
askKB :: (Monad m,
          IsFirstOrder fof, Ord fof, Pretty fof, lit ~ Marked Literal fof,
          Atom atom term v,
          HasApplyAndEquate atom,
          IsTerm term,
          HasSkolem function,
          Data fof, Typeable function,
          atom ~ AtomOf fof, term ~ TermOf atom, p ~ PredOf atom,
          function ~ FunOf term,
          v ~ VarOf fof, v ~ SVarOf function) =>
         fof -> ProverT' v term lit m Bool
askKB s = theoremKB s >>= return . fst

-- |See whether the sentence is true, false or invalid.  Return proofs
-- for truth and falsity.
validKB :: (IsFirstOrder fof, Ord fof, Pretty fof, lit ~ Marked Literal fof,
            Atom atom term v,
            HasApplyAndEquate atom,
            IsTerm term,
            HasSkolem function,
            Monad m, Data fof, Typeable function,
            atom ~ AtomOf fof, term ~ TermOf atom, p ~ PredOf atom,
            function ~ FunOf term,
            v ~ VarOf fof, v ~ SVarOf function) =>
           fof -> ProverT' v term lit m (ProofResult,
                                                                            SetOfSupport lit v term,
                                                                            SetOfSupport lit v term)
validKB s =
    theoremKB s >>= \ (proved, proof1) ->
    inconsistantKB s >>= \ (disproved, proof2) ->
    return (if proved then Proved else if disproved then Disproved else Invalid, proof1, proof2)

-- |Validate a sentence and insert it into the knowledgebase.  Returns
-- the INF sentences derived from the new sentence, or Nothing if the
-- new sentence is inconsistant with the current knowledgebase.
tellKB :: (IsFirstOrder fof, Ord fof, Pretty fof, lit ~ Marked Literal fof,
           Atom atom term v,
           HasApplyAndEquate atom,
           IsTerm term,
           HasSkolem function,
           Monad m, Data fof, Typeable function,
           atom ~ AtomOf fof, term ~ TermOf atom, p ~ PredOf atom,
           function ~ FunOf term,
           v ~ VarOf fof, v ~ SVarOf function) =>
          fof -> ProverT' v term lit m (Proof lit)
tellKB s =
    do st <- get
       inf <- lift (implicativeNormalForm s)
       let inf' = Set.map (withId (sentenceCount st)) inf
       (valid, _, _) <- validKB s
       case valid of
         Disproved -> return ()
         _ -> put st { knowledgeBase = Set.union (knowledgeBase st) inf'
                     , sentenceCount = sentenceCount st + 1 }
       return $ Proof {proofResult = valid, proof = Set.map wiItem inf'}

loadKB :: (IsFirstOrder fof, Ord fof, Pretty fof, lit ~ Marked Literal fof,
           Atom atom term v,
           IsTerm term,
           HasApplyAndEquate atom,
           HasSkolem function,
           Monad m, Data fof, Typeable function,
           atom ~ AtomOf fof, term ~ TermOf atom,
           function ~ FunOf term,
           v ~ VarOf fof, v ~ SVarOf function) =>
          [fof] -> StateT (ProverState (ImplicativeForm lit)) (SkolemT m (FunOf term)) [Proof lit]
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
    case Set.minView kb of
      Nothing -> "Nothing in Knowledge Base\n"
      Just (WithId {wiItem = x, wiIdent = n}, kb')
          | Set.null kb' ->
              show n ++ ") " ++ "\t" ++ show x ++ "\n"
          | True ->
              show n ++ ") " ++ "\t" ++ show x ++ "\n" ++ reportKB (st {knowledgeBase = kb'})
