import Common (TestFormula, TestProof, V, TFormula, TAtom, TTerm, doTest)
import System.Exit
import Test.HUnit
import qualified Data.Logic.Harrison.DP as DP
import qualified Data.Logic.Harrison.PropExamples as PropExamples
import qualified Harrison.Main as Harrison
import qualified Logic
import qualified Chiou0 as Chiou0
--import qualified Data.Logic.Tests.TPTP as TPTP
import qualified Data

main :: IO ()
main =
    runTestTT (TestList [Logic.tests,
                         Chiou0.tests,
                         -- TPTP.tests,  -- This has a problem in the rendering code - it loops
                         Data.tests formulas proofs,
                         Harrison.tests,
                         PropExamples.tests,
                         DP.tests]) >>=
    doCounts
    where
      doCounts counts' = exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
      -- Generate the test data with a particular instantiation of FirstOrderFormula.
      formulas = Data.allFormulas
      proofs = (Data.proofs :: [TestProof TFormula TTerm V])
