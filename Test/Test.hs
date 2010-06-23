module Main where

import System.Exit
import Test.HUnit
import qualified Test.Logic as Logic

main = runTestTT (TestList (Logic.tests)) >>= 
       \ counts -> exitWith (if errors counts /= 0 || failures counts /= 0 then ExitFailure 1 else ExitSuccess)
