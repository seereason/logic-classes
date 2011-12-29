{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Resolution where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Equals (AtomEq, pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Harrison.Normal (simpcnf)
import Data.Logic.Harrison.Resolution (resolution1, resolution2, presolution)
import Data.Logic.Normal.Skolem (runSkolem, skolemize)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual, Assertion)
import Data.Logic.Tests.Harrison.HUnit

tests :: TestFormulaEq formula atom term v p f => Test formula
tests = TestLabel "Data.Logic.Harrison.Resolution" $ TestList [test01, test02, test03, test04]

-- ------------------------------------------------------------------------- 
-- Barber's paradox is an example of why we need factoring.                  
-- ------------------------------------------------------------------------- 

test01 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test01 = TestCase $ assertEqual "Barber's paradox (p. 181)" expected input
    where input = simpcnf (runSkolem (skolemize((.~.)barb)))
          barb :: formula
          barb = exists (fromString "b") (for_all (fromString "x") (shaves [b, x] .<=>. ((.~.)(shaves [x, x]))))
          -- This is not exactly what is in the book
          expected = Set.fromList [Set.fromList [shaves [b,     fx [b]], (.~.)(shaves [fx [b],fx [b]])],
                                   Set.fromList [shaves [fx [b],fx [b]], (.~.)(shaves [b,     fx [b]])]]
          x = vt (fromString "x") :: term
          b = vt (fromString "b") :: term
          fx = fApp (fromString "f_x" :: f) :: [term] -> term
          shaves :: [term] -> formula
          shaves = pApp (fromString "shaves" :: p) 

-- ------------------------------------------------------------------------- 
-- Simple example that works well.                                           
-- ------------------------------------------------------------------------- 

test02 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test02 = TestCase $ assertEqual "Davis-Putnam example" expected input
    where input = runSkolem (resolution1 (dpExampleFm :: formula))
          expected = Set.singleton (Success True)

dpExampleFm :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => formula
dpExampleFm = exists x . exists y .for_all z $
              (f [vt x, vt y] .=>. (f [vt y, vt z] .&. f [vt z, vt z])) .&.
              ((f [vt x, vt y] .&. g [vt x, vt y]) .=>. (g [vt x, vt z] .&. g [vt z, vt z]))
    where
      x = fromString "x" :: v
      y = fromString "y" :: v
      z = fromString "z" :: v
      g = pApp (fromString "G")
      f = pApp (fromString "F")

-- ------------------------------------------------------------------------- 
-- This is now a lot quicker.                                                
-- ------------------------------------------------------------------------- 

test03 :: forall formula atom v p term f. TestFormulaEq formula atom term v p f => Test formula
test03 = TestCase $ assertEqual "Davis-Putnam example 2" expected input
    where input = runSkolem (resolution2 (dpExampleFm :: formula))
          expected = Set.singleton (Success True)

-- ------------------------------------------------------------------------- 
-- Example: the (in)famous Los problem.                                      
-- ------------------------------------------------------------------------- 

test04 :: forall formula atom v p term f. (FirstOrderFormula formula atom v,
                                           AtomEq atom p term,
                                           Term term v f, Eq formula, Ord formula, Eq p, Eq term,
                                           IsString v, IsString p, IsString f) =>
          Test formula
test04 = TestCase $ assertEqual "Los problem (p. 198)" expected input
    where input = runSkolem (presolution (losFm :: formula))
          expected = Set.fromList [Success True]

losFm :: forall formula atom v p term f. (FirstOrderFormula formula atom v,
                                          AtomEq atom p term,
                                          Term term v f, Eq formula, Ord formula, Eq p, Eq term,
                                          IsString v, IsString p, IsString f) => formula
losFm = (for_all x (for_all y (for_all z (p [vt x, vt y] .=>. p [vt y, vt z] .=>. p [vt x, vt z])))) .&.
        (for_all x (for_all y (for_all z (q [vt x, vt y] .=>. q [vt y, vt z] .=>. q [vt x, vt z])))) .&.
        (for_all x (for_all y (q [vt x, vt y] .=>. q [vt y, vt x]))) .&.
        (for_all x (for_all y (p [vt x, vt y] .|. q [vt x, vt y]))) .=>.
        (for_all x (for_all y (p [vt x, vt y]))) .|.
        (for_all x (for_all y (q [vt x, vt y])))
    where
      x = fromString "x" :: v
      y = fromString "y" :: v
      z = fromString "z" :: v
      p = pApp (fromString "P")
      q = pApp (fromString "Q")
