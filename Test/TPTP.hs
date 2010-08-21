module Test.TPTP where
    
import Codec.TPTP (Formula)
import Logic.FirstOrder (conj)
import Logic.Instances.TPTP
import Logic.Monad (runNormal)
import Logic.Logic (Logic ((.~.), (.=>.)))
import Logic.NormalForm (cnfTrace)
import Test.Data (chang43KB, chang43Conjecture)
import Test.HUnit
import Test.Types (TestFormula(formula))

tests :: Test
tests = TestLabel "TPTP" $ TestList [tptp]

tptp :: Test
tptp =
    TestCase (assertEqual "tptp cnf trace" "abc" (runNormal (cnfTrace f)))
    where
      f :: Formula
      f = (.~.) (conj (map formula (snd (chang43KB :: (String, [TestFormula Formula])))) .=>.
                 formula chang43Conjecture)
