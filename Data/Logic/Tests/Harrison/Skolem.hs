{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Skolem
    ( tests
    ) where

import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Constants (false)
import Data.Logic.Classes.Equals (pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(exists, for_all))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Harrison.Skolem (simplify, nnf, pnf)
import Data.Logic.Harrison.Skolem (runSkolem, skolemize)
import Data.Logic.Tests.HUnit ()
import Data.Logic.Types.Harrison.Equal (FOLEQ, PredName(..))
import Data.Logic.Types.Harrison.FOL (Function(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula)
import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Skolem" $ TestList [test01, test02, test03, test04, test05]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestCase $ assertEqual "simplify (p. 140)" expected input
    where p = Named "P"
          q = Named "Q"
          input = simplify fm
          expected = (for_all "x" (pApp p [vt "x"])) .=>. (pApp q []) :: Formula FOLEQ
          fm :: Formula FOLEQ
          fm = (for_all "x" (for_all "y" (pApp p [vt "x"] .|. (pApp p [vt "y"] .&. false)))) .=>. exists "z" (pApp q [])

-- ------------------------------------------------------------------------- 
-- Example of NNF function in action.                                        
-- ------------------------------------------------------------------------- 

test02 :: Test
test02 = TestCase $ assertEqual "nnf (p. 140)" expected input
    where p = Named "P"
          q = Named "Q"
          input = nnf fm
          expected = exists "x" ((.~.)(pApp p [vt "x"])) .|.
                     ((exists "y" (pApp q [vt "y"]) .&. exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))) .|.
                      (for_all "y" ((.~.)(pApp q [vt "y"])) .&.
                       for_all "z" (((.~.)(pApp p [vt "z"])) .|. ((.~.)(pApp q [vt "z"])))))
          fm :: Formula FOLEQ
          fm = (for_all "x" (pApp p [vt "x"])) .=>. ((exists "y" (pApp q [vt "y"])) .<=>. exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"]))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test03 :: Test
test03 = TestCase $ assertEqual "pnf (p. 144)" expected input
    where p = Named "P"
          q = Named "Q"
          r = Named "R"
          input = pnf fm
          expected = exists "x" (for_all "z"
                                 ((((.~.)(pApp p [vt "x"])) .&. ((.~.)(pApp r [vt "y"]))) .|.
                                  ((pApp q [vt "x"]) .|.
                                   (((.~.)(pApp p [vt "z"])) .|.
                                    ((.~.)(pApp q [vt "z"]))))))
          fm :: Formula FOLEQ
          fm = (for_all "x" (pApp p [vt "x"]) .|. (pApp r [vt "y"])) .=>.
               exists "y" (exists "z" ((pApp q [vt "y"]) .|. ((.~.)(exists "z" (pApp p [vt "z"] .&. pApp q [vt "z"])))))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test04 :: Test
test04 = TestCase $ assertEqual "skolemize 1 (p. 150)" expected input
    where input = runSkolem (skolemize id fm) :: Formula FOLEQ
          fm :: Formula FOLEQ
          fm = exists "y" (pApp (Named "<") [vt "x", vt "y"] .=>.
                           for_all "u" (exists "v" (pApp (Named "<") [fApp "*" [vt "x", vt "u"],  fApp "*" [vt "y", vt "v"]])))
          expected = ((.~.)(pApp (Named "<") [vt "x",fApp (Skolem 1) [vt "x"]])) .|.
                     (pApp (Named "<") [fApp "*" [vt "x",vt "u"],fApp "*" [fApp (Skolem 1) [vt "x"],fApp (Skolem 2) [vt "u",vt "x"]]])

test05 :: Test
test05 = TestCase $ assertEqual "skolemize 2 (p. 150)" expected input
    where p = Named "P"
          q = Named "Q"
          input = runSkolem (skolemize id fm) :: Formula FOLEQ
          fm :: Formula FOLEQ
          fm = for_all "x" ((pApp p [vt "x"]) .=>.
                            (exists "y" (exists "z" ((pApp q [vt "y"]) .|.
                                                     ((.~.)(exists "z" ((pApp p [vt "z"]) .&. (pApp q [vt "z"]))))))))
          expected = ((.~.)(pApp p [vt "x"])) .|.
                     ((pApp q [fApp (Skolem 1) []]) .|.
                      (((.~.)(pApp p [vt "z"])) .|.
                       ((.~.)(pApp q [vt "z"]))))
