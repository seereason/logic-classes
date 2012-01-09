{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Resolution where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Equals (pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Harrison.Normal (simpcnf)
import Data.Logic.Harrison.Resolution (resolution1, resolution2, presolution)
import Data.Logic.Harrison.Skolem (runSkolem, skolemize)
import Data.Logic.Harrison.Tableaux (unifyAtomsEq)
import Data.Logic.Types.Harrison.Equal (FOLEQ)
import Data.Logic.Types.Harrison.FOL (Function(Skolem))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual, Assertion)
import Data.Logic.Tests.Harrison.HUnit

tests :: Test (Formula FOLEQ)
tests = TestLabel "Data.Logic.Tests.Harrison.Resolution" $ TestList [test01, test02, test03, test04]

-- ------------------------------------------------------------------------- 
-- Barber's paradox is an example of why we need factoring.                  
-- ------------------------------------------------------------------------- 

test01 :: Test (Formula FOLEQ)
test01 = TestCase $ assertEqual "Barber's paradox (p. 181)" expected input
    where input = simpcnf (runSkolem (skolemize ((.~.)barb)))
          barb :: Formula FOLEQ
          barb = exists (fromString "b") (for_all (fromString "x") (shaves [b, x] .<=>. ((.~.)(shaves [x, x]))))
          -- This is not exactly what is in the book
          expected = Set.fromList [Set.fromList [shaves [b,     fx [b]], (.~.)(shaves [fx [b],fx [b]])],
                                   Set.fromList [shaves [fx [b],fx [b]], (.~.)(shaves [b,     fx [b]])]]
          x = vt (fromString "x")
          b = vt (fromString "b")
          fx = fApp (Skolem 1)
          shaves = pApp (fromString "shaves") 

-- ------------------------------------------------------------------------- 
-- Simple example that works well.                                           
-- ------------------------------------------------------------------------- 

test02 :: Test (Formula FOLEQ)
test02 = TestCase $ assertEqual "Davis-Putnam example" expected input
    where input = runSkolem (resolution1 unifyAtomsEq (dpExampleFm :: Formula FOLEQ))
          expected = Set.singleton (Success True)

dpExampleFm :: Formula FOLEQ
dpExampleFm = exists x . exists y .for_all z $
              (f [vt x, vt y] .=>. (f [vt y, vt z] .&. f [vt z, vt z])) .&.
              ((f [vt x, vt y] .&. g [vt x, vt y]) .=>. (g [vt x, vt z] .&. g [vt z, vt z]))
    where
      x = fromString "x"
      y = fromString "y"
      z = fromString "z"
      g = pApp (fromString "G")
      f = pApp (fromString "F")

-- ------------------------------------------------------------------------- 
-- This is now a lot quicker.                                                
-- ------------------------------------------------------------------------- 

test03 :: Test (Formula FOLEQ)
test03 = TestCase $ assertEqual "Davis-Putnam example 2" expected input
    where input = runSkolem (resolution2 (dpExampleFm :: Formula FOLEQ))
          expected = Set.singleton (Success True)

-- ------------------------------------------------------------------------- 
-- Example: the (in)famous Los problem.                                      
-- ------------------------------------------------------------------------- 

test04 :: Test (Formula FOLEQ)
test04 = TestCase $ assertEqual "Los problem (p. 198)" expected input
    where input = runSkolem (presolution losFm)
          expected = Set.fromList [Success True]

losFm :: Formula FOLEQ
losFm = (for_all x (for_all y (for_all z (p [vt x, vt y] .=>. p [vt y, vt z] .=>. p [vt x, vt z])))) .&.
        (for_all x (for_all y (for_all z (q [vt x, vt y] .=>. q [vt y, vt z] .=>. q [vt x, vt z])))) .&.
        (for_all x (for_all y (q [vt x, vt y] .=>. q [vt y, vt x]))) .&.
        (for_all x (for_all y (p [vt x, vt y] .|. q [vt x, vt y]))) .=>.
        (for_all x (for_all y (p [vt x, vt y]))) .|.
        (for_all x (for_all y (q [vt x, vt y])))
    where
      x = fromString "x"
      y = fromString "y"
      z = fromString "z"
      p = pApp (fromString "P")
      q = pApp (fromString "Q")
