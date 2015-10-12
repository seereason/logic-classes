{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall #-}
module Harrison.Resolution where

import Data.Logic.Classes.Apply (pApp)
import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Combine (IsCombinable(..))
import Data.Logic.Classes.FirstOrder (IsQuantified(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (IsTerm(vt, fApp))
import Data.Logic.Harrison.Normal (simpcnf)
import Data.Logic.Harrison.Resolution (resolution1, resolution2, resolution3, presolution)
import Data.Logic.Harrison.Skolem (runSkolem, skolemize)
import Data.Logic.Types.Harrison.Equal (FOLEQ)
import Data.Logic.Types.Harrison.FOL (Function(Skolem), TermType)
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula)
import qualified Data.Set as Set
import Data.String (IsString(..))
import Prelude hiding (negate)
import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Resolution" $
        TestList [test01, test02, test03, test04, test05]

-- ------------------------------------------------------------------------- 
-- Barber's paradox is an example of why we need factoring.                  
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestCase $ assertEqual "Barber's paradox (p. 181)" expected input
    where input = simpcnf (runSkolem (skolemize id ((.~.)barb)))
          barb :: Formula FOLEQ
          barb = exists (fromString "b") (for_all (fromString "x") (shaves [b, x] .<=>. ((.~.)(shaves [x, x]))))
          -- This is not exactly what is in the book
          expected = Set.fromList [Set.fromList [shaves [b,     fx [b]], (.~.)(shaves [fx [b],fx [b]])],
                                   Set.fromList [shaves [fx [b],fx [b]], (.~.)(shaves [b,     fx [b]])]]
          x = vt (fromString "x")
          b = vt (fromString "b")
          fx = fApp (Skolem "x")
          shaves = pApp (fromString "shaves") 

-- ------------------------------------------------------------------------- 
-- Simple example that works well.                                           
-- ------------------------------------------------------------------------- 

test02 :: Test
test02 = TestCase $ assertEqual "Davis-Putnam example" expected input
    where input = runSkolem (resolution1 (dpExampleFm :: Formula FOLEQ))
          expected = Set.singleton (Success True)

dpExampleFm :: Formula FOLEQ
dpExampleFm = exists "x" . exists "y" .for_all "z" $
              (f [x, y] .=>. (f [y, z] .&. f [z, z])) .&.
              ((f [x, y] .&. g [x, y]) .=>. (g [x, z] .&. g [z, z]))
    where
      x = vt "x" :: TermType
      y = vt "y"
      z = vt "z"
      g = pApp "G" :: [TermType] -> Formula FOLEQ
      f = pApp "F"

-- ------------------------------------------------------------------------- 
-- This is now a lot quicker.                                                
-- ------------------------------------------------------------------------- 

test03 :: Test
test03 = TestCase $ assertEqual "Davis-Putnam example 2" expected input
    where input = runSkolem (resolution2 (dpExampleFm :: Formula FOLEQ))
          expected = Set.singleton (Success True)

-- ------------------------------------------------------------------------- 
-- Example: the (in)famous Los problem.                                      
-- ------------------------------------------------------------------------- 

test04 :: Test
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

test05 :: Test
test05 = TestCase $ assertEqual "Socrates syllogism" expected input
    where input = (runSkolem (resolution1 socrates),
                   runSkolem (resolution2 socrates),
                   runSkolem (resolution3 socrates),
                   runSkolem (presolution socrates),
                   runSkolem (resolution1 notSocrates),
                   runSkolem (resolution2 notSocrates),
                   runSkolem (resolution3 notSocrates),
                   runSkolem (presolution notSocrates))
          expected = (Set.singleton (Success True),
                      Set.singleton (Success True),
                      Set.singleton (Success True),
                      Set.singleton (Success True),
                      Set.singleton (Success {-False-} True),
                      Set.singleton (Success {-False-} True),
                      Set.singleton (Failure ["No proof found"]),
                      Set.singleton (Success {-False-} True))

socrates :: Formula FOLEQ
socrates =
    (for_all x (s [vt x] .=>. h [vt x]) .&. for_all x (h [vt x] .=>. m [vt x])) .=>. for_all x (s [vt x] .=>. m [vt x])
    where
      x = fromString "x"
      s = pApp (fromString "S")
      h = pApp (fromString "H")
      m = pApp (fromString "M")

notSocrates :: Formula FOLEQ
notSocrates =
    (for_all x (s [vt x] .=>. h [vt x]) .&. for_all x (h [vt x] .=>. m [vt x])) .=>. for_all x (s [vt x] .=>.  ((.~.)(m [vt x])))
    where
      x = fromString "x"
      s = pApp (fromString "S")
      h = pApp (fromString "H")
      m = pApp (fromString "M")
