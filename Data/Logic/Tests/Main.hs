import Data.Logic.Tests.Common (TestFormula, TestProof, V, TFormula, TAtom, TTerm)
import System.Exit
import Test.HUnit
import qualified Data.Logic.Harrison.PropExamples as PropExamples
import qualified Data.Logic.Tests.Harrison.Main as Harrison
import qualified Data.Logic.Tests.Logic as Logic
import qualified Data.Logic.Tests.Chiou0 as Chiou0
--import qualified Data.Logic.Tests.TPTP as TPTP
import qualified Data.Logic.Tests.Data as Data

main :: IO ()
main =
    runTestTT (TestList [Logic.tests,
                         Chiou0.tests,
                         -- TPTP.tests,  -- This has a problem in the rendering code - it loops
                         Data.tests formulas proofs,
                         Harrison.tests,
                         PropExamples.tests]) >>=
    doCounts
    where
      doCounts counts' = exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
      -- Generate the test data with a particular instantiation of FirstOrderFormula.
      formulas = (Data.allFormulas :: [TestFormula TFormula TAtom V])
      proofs = (Data.proofs :: [TestProof TFormula TTerm V])
