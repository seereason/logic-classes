import System.Exit
import Test.HUnit
import Logic.Instances.Native
import Logic.Normal (ImplicativeNormalForm)
import Logic.Pretty (showForm)
import qualified Test.Logic as Logic
import qualified Test.Chiou0 as Chiou0
--import qualified Test.TPTP as TPTP
import Test.Types (TestFormula, TestProof, V, Pr, AtomicFunction, TFormula, TTerm)
import qualified Test.Data as Data

main :: IO ()
main =
    runTestTT (TestList [Logic.tests,
                         Chiou0.tests,
                         -- TPTP.tests,  -- This has a problem in the rendering code - it loops
                         Data.tests formulas proofs]) >>=
    doCounts
    where
      doCounts counts' = exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
      -- Generate the test data with a particular instantiation of FirstOrderFormula.
      formulas = (Data.allFormulas :: [TestFormula TFormula TTerm V Pr AtomicFunction])
      proofs = (Data.proofs :: [TestProof TFormula TTerm V])
