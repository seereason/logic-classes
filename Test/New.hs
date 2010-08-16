{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module Test.New where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Generics (Data, Typeable, listify)
import qualified Data.Set as S
import Logic.FirstOrder (FirstOrderLogic, convertFOF, fromSkolem)
import Logic.Instances.Chiou ()
import Logic.KnowledgeBase (loadKB, theoremKB, getKB)
import Logic.Logic (Logic(..))
import Logic.Monad (runNormal, runProver')
import Logic.NormalForm (clausalNormalForm, prenexNormalForm, disjunctiveNormalForm, skolemNormalForm, negationNormalForm)
import Logic.Satisfiable (satisfiable) 
--import PropLogic (PropForm(..), TruthTable, truthTable)
import Test.Data
import Test.HUnit
import Test.Types
--import qualified TextDisplay as TD

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

tests = TestLabel "New" $ TestList (concatMap doFormula (formulas ++
                                                         gFind (animalKB, chang43KB) ++
                                                         animalConjectures ++
                                                         [chang43Conjecture, chang43ConjectureRenamed]) ++
                                    concatMap doProofs proofs)
    where
      doFormula f = concatMap (doTest f) (expected f)
      doProofs p = map (doProof p) (proofExpected p) 

-- mkQ :: (Typeable a, Typeable b) => r -> (b -> r) -> a -> r

skolemSet :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> S.Set Int
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins f s = case fromSkolem f of
                  Just n -> S.insert n s
                  Nothing -> s
      skolemList :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

--skolemNumber :: (Data v, Typeable v, Data f, Typeable f, Skolem f) => Term v f -> [Int]
skolemNumber :: FirstOrderLogic formula term v p f => f -> [Int]
skolemNumber f = maybe [] (: []) (fromSkolem f)

doTest f (FirstOrderFormula f') =
    [TestCase (assertEqual (name f ++ " original formula") f' (formula f))]
doTest f (ClausalNormalForm fss) =
    [TestCase (assertEqual (name f ++ " clausal normal form") fss (runNormal (clausalNormalForm (formula f))))]
doTest f (PrenexNormalForm f') =
    [TestCase (assertEqual (name f ++ " prenex normal form") f' (runNormal (prenexNormalForm (formula f))))]
doTest f (DisjunctiveNormalForm f') =
    [TestCase (assertEqual (name f ++ " disjunctive normal form") f' (runNormal (disjunctiveNormalForm (formula f))))]
doTest f (NegationNormalForm f') =
    [TestCase (assertEqual (name f ++ " negation normal form") f' (runNormal (negationNormalForm (formula f))))]
doTest f (SkolemNormalForm f') =
    [TestCase (assertEqual (name f ++ " skolem normal form") f' (runNormal (skolemNormalForm (formula f))))]
doTest f (SkolemNumbers f') =
    [TestCase (assertEqual (name f ++ " skolem numbers") f' (skolemSet (runNormal (skolemNormalForm (formula f)))))]
doTest f (ConvertToChiou result) =
    [TestCase (assertEqual (name f ++ " converted to Chiou") result (convertFOF id id id (formula f)))]
doTest f (SatChiou result) =
    [TestCase (assertEqual (name f ++ " Chiou.satisfiable") result (head (runProver' (loadKB [convertFOF id id id (formula f)]))))]
doTest f (SatPropLogic result) =
    [TestCase (assertEqual (name f ++ " satisfiable") result (runNormal (satisfiable (formula f))))]

doProof p (ChiouResult result) =
    TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
    [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover")
                           result
                           (runProver' (loadKB (snd (proofKnowledge p)) >> theoremKB (conjecture p))))]
doProof p (ChiouKB result) =
    TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
    [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base")
                           result
                           (runProver' (loadKB (snd (proofKnowledge p)) >> getKB)))]

-- Knowledge Base tests.
kbTests :: (String, [TestFormula], [TestFormula]) -> [Test]
kbTests (kbname, knowledge, conjectures) =
    concatMap conjectureTests conjectures
    where
      conjectureTests c = concatMap (conjectureTest c) (expected c)
      conjectureTest c expect =
          doTest (c { name = name c ++ " with " ++ kbname ++ " knowledge base"
                    , formula = conj (map formula knowledge) .=>. formula c }) expect
{-
          [TestCase (assertEqual
                     (name f ++ " conjecture")
                     result
                     (runLiteralMap (theorem sat1 (conj (map formula knowledge ++ [formula f])))))]
      conjectureTest f _ = []
-}
      conj [] = error "conj []"
      conj [x] = x
      conj (x:xs) = x .&. conj xs
