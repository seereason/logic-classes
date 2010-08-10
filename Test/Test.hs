import System.Exit
import Test.HUnit
import qualified Test.Logic as Logic
import qualified Test.Chiou0 as Chiou0
import qualified Test.Chiou as Chiou
import qualified Test.New as New

main :: IO ()
main = runTestTT (TestList [Logic.tests, Chiou0.tests, Chiou.tests]) >>= 
       \ counts' -> exitWith (if errors counts' /= 0 || failures counts' /= 0 then ExitFailure 1 else ExitSuccess)
