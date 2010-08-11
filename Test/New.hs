{-# LANGUAGE DeriveDataTypeable, OverloadedStrings, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS -Wwarn -fno-warn-missing-signatures #-}
module Test.New where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Generics (Data, Typeable, listify)
import Logic.Chiou.Monad (runProver)
import qualified Logic.Chiou.KnowledgeBase as C
import Logic.FirstOrder (convertFOF)
import Logic.Logic (Logic(..))
import Logic.Monad (runSkolem, runLiteralMap)
import Logic.NormalForm (clausalNormalForm, clausalNormalForm', prenexNormalForm, disjunctiveNormalForm, skolemNormalForm, negationNormalForm)
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

tests = TestLabel "New" $ TestList (concatMap doFormula (formulas ++ gFind (animalKB, chang43KB) ++ animalConjectures ++ [chang43Conjecture, chang43ConjectureRenamed]) ++
                                    concatMap doProofs proofs)
    where
      doFormula f = concatMap (doTest f) (expected f)
      doProofs p = map (doProof p) (proofExpected p) 

doTest f (FirstOrderFormula f') =
    [TestCase (assertEqual (name f) f' (formula f))]
doTest f (ClausalNormalForm fss) =
    [TestCase (assertEqual (name f ++ " clausal normal form") fss ({-runSkolem-} (clausalNormalForm' (formula f))))]
doTest f (PrenexNormalForm f') =
    [TestCase (assertEqual (name f ++ " prenex normal form") f' (prenexNormalForm (formula f)))]
doTest f (DisjunctiveNormalForm f') =
    [TestCase (assertEqual (name f ++ " disjunctive normal form") f' (disjunctiveNormalForm (formula f)))]
doTest f (NegationNormalForm f') =
    [TestCase (assertEqual (name f ++ " negation normal form") f' (negationNormalForm (formula f)))]
doTest f (SkolemNormalForm f') =
    [TestCase (assertEqual (name f ++ " skolem normal form") f' ({-runSkolem-} (skolemNormalForm (formula f))))]
doTest f (SatResult result) =
    [TestCase (assertEqual (name f ++ " satisfiable") result ({-runLiteralMap-} (satisfiable (formula f))))]
doTest f (ConvertToChiou result) =
    [TestCase (assertEqual (name f ++ " converted to Chiou") result (convertFOF id id id (formula f)))]

doProof p (ChiouResult result) =
    TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
    [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p))
                           result
                           (runProver (C.loadKB (snd (proofKnowledge p)) >> C.theoremKB (conjecture p))))]

-- Knowledge Base tests.
kbTests :: (String, [TestFormula], [TestFormula]) -> [Test]
kbTests (kbname, knowledge, conjectures) =
    concatMap conjectureTests conjectures
    where
      conjectureTests conjecture = concatMap (conjectureTest conjecture) (expected conjecture)
      conjectureTest conjecture expect =
          doTest (conjecture { name = name conjecture ++ " with " ++ kbname ++ " knowledge base"
                             , formula = conj (map formula knowledge) .=>. formula conjecture }) expect
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
