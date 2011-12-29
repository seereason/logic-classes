{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Resolution where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), pApp)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Harrison.Normal (simpcnf)
import Data.Logic.Harrison.Resolution (resolution1, resolution2, presolution)
import Data.Logic.Harrison.Skolem (skolemize)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual, Assertion)
import Data.Logic.Tests.Harrison.HUnit

tests :: TestFormula formula atom term v p f => Test formula
tests = TestLabel "Data.Logic.Harrison.Resolution" $ TestList [test01, test02, test03, test04]

-- ------------------------------------------------------------------------- 
-- Barber's paradox is an example of why we need factoring.                  
-- ------------------------------------------------------------------------- 

test01 :: forall formula atom term v p f. TestFormula formula atom term v p f => Test formula
test01 = TestCase $ assertEqual "Barber's paradox (p. 181)" expected input
    where input = simpcnf (skolemize((.~.)barb))
          barb :: formula
          barb = exists "b" (for_all "x" (shaves [b, x] .<=>. ((.~.)(shaves [x, x]))))
          -- This is not exactly what is in the book
          expected = Set.fromList [Set.fromList [shaves [b,     fx [b]], (.~.)(shaves [fx [b],fx [b]])],
                                   Set.fromList [shaves [fx [b],fx [b]], (.~.)(shaves [b,     fx [b]])]]
          x = vt "x"
          b = vt "b"
          fx = fApp "f_x"
          shaves = pApp "shaves"

-- ------------------------------------------------------------------------- 
-- Simple example that works well.                                           
-- ------------------------------------------------------------------------- 

test02 :: forall formula atom term v p f. TestFormula formula atom term v p f => Test formula
test02 = TestCase $ assertEqual "Davis-Putnam example" expected input
    where input = resolution1 (dpExampleFm :: formula)
          expected = Set.singleton (Success True)

dpExampleFm :: TestFormula formula atom term v p f => formula
dpExampleFm = exists "x" . exists "y" .for_all "z" $
              (pApp "F" [vt "x", vt "y"] .=>. (pApp "F" [vt "y", vt "z"] .&. pApp "F" [vt "z", vt "z"])) .&.
              ((pApp "F" [vt "x", vt "y"] .&. pApp "G" [vt "x", vt "y"]) .=>. (pApp "G" [vt "x", vt "z"] .&. pApp "G" [vt "z", vt "z"]))

-- ------------------------------------------------------------------------- 
-- This is now a lot quicker.                                                
-- ------------------------------------------------------------------------- 

test03 :: forall formula atom v p term f. TestFormula formula atom term v p f => Test formula
test03 = TestCase $ assertEqual "Davis-Putnam example 2" expected input
    where input = resolution2 (dpExampleFm :: formula)
          expected = Set.singleton (Success True)

-- ------------------------------------------------------------------------- 
-- Example: the (in)famous Los problem.                                      
-- ------------------------------------------------------------------------- 

test04 :: forall formula atom v p term f. (FirstOrderFormula formula atom v,
                                           Atom atom p term,
                                           Term term v f, Eq formula, Ord formula, Eq p, Eq term,
                                           IsString v, IsString p, IsString f) =>
          Test formula
test04 = TestCase $ assertEqual "Los problem (p. 198)" expected input
    where input = presolution (losFm :: formula)
          expected = Set.fromList [Success True]

losFm :: forall formula atom v p term f. (FirstOrderFormula formula atom v,
                                          Atom atom p term,
                                          Term term v f, Eq formula, Ord formula, Eq p, Eq term,
                                          IsString v, IsString p, IsString f) => formula
losFm = (for_all "x" (for_all "y" (for_all "z" (pApp "P" [vt "x", vt "y"] .=>. pApp "P" [vt "y", vt "z"] .=>. pApp "P" [vt "x", vt "z"])))) .&.
        (for_all "x" (for_all "y" (for_all "z" (pApp "Q" [vt "x", vt "y"] .=>. pApp "Q" [vt "y", vt "z"] .=>. pApp "Q" [vt "x", vt "z"])))) .&.
        (for_all "x" (for_all "y" (pApp "Q" [vt "x", vt "y"] .=>. pApp "Q" [vt "y", vt "x"]))) .&.
        (for_all "x" (for_all "y" (pApp "P" [vt "x", vt "y"] .|. pApp "Q" [vt "x", vt "y"]))) .=>.
        (for_all "x" (for_all "y" (pApp "P" [vt "x", vt "y"]))) .|.
        (for_all "x" (for_all "y" (pApp "Q" [vt "x", vt "y"])))
