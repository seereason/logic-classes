{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module Test.New where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Generics (Data, Typeable, listify)
import qualified Data.Set as S
import Logic.FirstOrder (FirstOrderLogic, convertFOF, fromSkolem)
import Logic.Implicative (Implicative)
import Logic.KnowledgeBase (loadKB, theoremKB, getKB)
import Logic.Logic (Logic(..))
import Logic.Monad (runNormal, runProver')
import Logic.NormalForm (clausalNormalForm, prenexNormalForm, disjunctiveNormalForm, skolemNormalForm, negationNormalForm)
import Logic.Satisfiable (satisfiable) 
import Test.HUnit
import Test.Types

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

tests :: (FirstOrderLogic formula term v p f, Implicative inf formula, Show term) =>
         [TestFormula formula] -> [TestProof inf formula term v] -> Test
tests fs ps =
    TestLabel "New" $ TestList (concatMap doTest fs ++ concatMap doProof ps)

skolemSet :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> S.Set Int
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins f s = case fromSkolem f of
                  Just n -> S.insert n s
                  Nothing -> s
      skolemList :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

skolemNumber :: FirstOrderLogic formula term v p f => f -> [Int]
skolemNumber f = maybe [] (: []) (fromSkolem f)

doTest :: forall formula term v p f. (FirstOrderLogic formula term v p f, Data formula) =>
          TestFormula formula -> [Test]
doTest f =
    concatMap doExpected (expected f)
    where
      doExpected (FirstOrderFormula f') =
          [TestCase (assertEqual (name f ++ " original formula") f' (formula f))]
      doExpected (ClausalNormalForm fss) =
          [TestCase (assertEqual (name f ++ " clausal normal form") fss (runNormal (clausalNormalForm (formula f))))]
      doExpected (PrenexNormalForm f') =
          [TestCase (assertEqual (name f ++ " prenex normal form") f' (runNormal (prenexNormalForm (formula f))))]
      doExpected (DisjunctiveNormalForm f') =
          [TestCase (assertEqual (name f ++ " disjunctive normal form") f' (runNormal (disjunctiveNormalForm (formula f))))]
      doExpected (NegationNormalForm f') =
          [TestCase (assertEqual (name f ++ " negation normal form") f' (runNormal (negationNormalForm (formula f))))]
      doExpected (SkolemNormalForm f') =
          [TestCase (assertEqual (name f ++ " skolem normal form") f' (runNormal (skolemNormalForm (formula f))))]
      doExpected (SkolemNumbers f') =
          [TestCase (assertEqual (name f ++ " skolem numbers") f' (skolemSet (runNormal (skolemNormalForm (formula f)))))]
      doExpected (ConvertToChiou result) =
          [TestCase (assertEqual (name f ++ " converted to Chiou") result (convertFOF id id id (formula f)))]
      --doExpected (SatChiou result) =
      --    [TestCase (assertEqual (name f ++ " Chiou.satisfiable") result (head (runProver' (loadKB [{-convertFOF id id id-} (formula f)]))))]
      doExpected (SatPropLogic result) =
          [TestCase (assertEqual (name f ++ " satisfiable") result (runNormal (satisfiable (formula f))))]

doProof :: forall inf formula term v p f. (FirstOrderLogic formula term v p f, Implicative inf formula, Show inf, Show term) =>
           TestProof inf formula term v -> [Test]
doProof p =
    concatMap doExpected (proofExpected p)
    where
      doExpected (ChiouResult result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover")
                      result
                      (runProver' (loadKB kb >> theoremKB c)))]]
      doExpected (ChiouKB result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base")
                      result
                      (runProver' (loadKB kb >> getKB)))]]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula

-- Knowledge Base tests.
kbTests :: (FirstOrderLogic formula term v p f, Show formula, Data formula, Ord formula) =>
           (String, [TestFormula formula], [TestFormula formula]) -> [Test]
kbTests (kbname, knowledge, conjectures) =
    concatMap conjectureTests conjectures
    where
      conjectureTests c =
          doTest (c { name = name c ++ " with " ++ kbname ++ " knowledge base"
                    , formula = conj (map formula knowledge) .=>. formula c })
      conj [] = error "conj []"
      conj [x] = x
      conj (x:xs) = x .&. conj xs
