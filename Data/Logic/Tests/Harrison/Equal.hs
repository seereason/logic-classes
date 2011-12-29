{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Equal where

-- ========================================================================= 
-- First order logic with equality.                                          
--                                                                           
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Combine (Combinable(..), (∧), (⇒))
import Data.Logic.Classes.Equals ((.=.))
import Data.Logic.Classes.FirstOrder (pApp, (∃), (∀))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Harrison.Equal (equalitize, function_congruence)
import Data.Logic.Harrison.Meson (meson)
import Data.Logic.Normal.Skolem (runSkolem)
import Data.Logic.Types.Harrison.FOL (TermType(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import Data.Logic.Types.Harrison.Equal (FOLEQ(..), PredName(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String (IsString(fromString))
-- import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)
import Data.Logic.Tests.Harrison.HUnit

tests :: TestFormulaEq formula atom term v p f => Test formula
tests = TestLabel "Data.Logic.Tests.Harrison.Equal" $ TestList [test01, test02, test03, test04]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test01 = TestCase $ assertEqual "function_congruence" expected input
    where input = map function_congruence [(fromString "f", 3 :: Int), (fromString "+",2)]
          expected :: [Set.Set formula]
          expected = [Set.fromList
                      [(∀) x1
                       ((∀) x2
                        ((∀) x3
                         ((∀) y1
                          ((∀) y2
                           ((∀) y3 ((((vt x1) .=. (vt y1)) ∧ (((vt x2) .=. (vt y2)) ∧ ((vt x3) .=. (vt y3)))) ⇒
                                          ((fApp (fromString "f") [vt x1,vt x2,vt x3]) .=. (fApp (fromString "f") [vt y1,vt y2,vt y3]))))))))],
                      Set.fromList
                      [(∀) x1
                       ((∀) x2
                        ((∀) y1
                         ((∀) y2 ((((vt x1) .=. (vt y1)) ∧ ((vt x2) .=. (vt y2))) ⇒
                                        ((fApp (fromString "+") [vt x1,vt x2]) .=. (fApp (fromString "+") [vt y1,vt y2]))))))]]
          x1 = fromString "x1"
          x2 = fromString "x2"
          x3 = fromString "x3"
          y1 = fromString "y1"
          y2 = fromString "y2"
          y3 = fromString "y3"

-- ------------------------------------------------------------------------- 
-- A simple example (see EWD1266a and the application to Morley's theorem).  
-- ------------------------------------------------------------------------- 

test :: forall formula atom term v p f a. (TestFormulaEq formula atom term v p f, Show a, Eq a) => String -> a -> a -> Test formula
test label expected input = TestLabel label $ TestCase $ assertEqual label expected input

test02 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test02 = test "equalitize 1 (p. 241)" expected input
    where input = runSkolem (meson (Just 5) ewd)
          ewd = equalitize fm
          fm :: Formula FOLEQ
          fm = ((∀) x (fx ⇒ gx)) ∧ ((∃) x fx) ∧ ((∀) x ((∀) y (gx ∧ gy ⇒ vt x .=. vt y))) ⇒
               (∀) y gy ⇒ fy
          fx = pApp (Named "f") [vt x]
          gx = pApp (Named "g") [vt x]
          fy = pApp (Named "f") [vt y]
          gy = pApp (Named "g") [vt y]
          x = fromString "x"
          y = fromString "y"
          expected = Set.singleton (Success ((Map.fromList [("_0",vt' "_2"),
                                                            ("_1",fApp' "c_y" []),
                                                            ("_2",vt' "_4"),
                                                            ("_3",fApp' "c_y" []),
                                                            ("_4",fApp' "c_x" []),
                                                            ("_5",fApp' "c_y" [])], 0, 6), 5))
          fApp' = fApp . fromString
          vt' = vt . fromString

-- ------------------------------------------------------------------------- 
-- Wishnu Prasetya's example (even nicer with an "exists unique" primitive). 
-- ------------------------------------------------------------------------- 

test03 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test03 = TestLabel "equalitize 2" $ TestCase $ assertEqual "equalitize 2 (p. 241)" expected input
    where input = runSkolem (meson (Just 1) wishnu)
          wishnu = equalitize fm
          fm :: Formula FOLEQ
          fm = ((∃) (fromString "x") ((x .=. f[g[x]]) ∧ (∀) (fromString "x'") ((x' .=. f[g[x']]) ⇒ (x .=. x')))) .<=>.
               ((∃) (fromString "y") ((y .=. g[f[y]]) ∧ (∀) (fromString "y'") ((y' .=. g[f[y']]) ⇒ (y .=. y'))))
          x = vt (fromString "x")
          y = vt (fromString "y")
          x' = vt (fromString "x'")
          y' = vt (fromString "y")
          f terms = fApp (fromString "f") terms
          g terms = fApp (fromString "g") terms
          expected = Set.singleton (Failure ["Exceeded maximum depth limit"])

-- ------------------------------------------------------------------------- 
-- More challenging equational problems. (Size 18, 61814 seconds.)           
-- ------------------------------------------------------------------------- 

test04 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test04 = test "equalitize 3 (p. 248)" expected input
    where
      input = runSkolem (meson (Just 50) . equalitize $ fm)
      fm :: Formula FOLEQ
      fm = ((∀) "x" . (∀) "y" . (∀) "z") ((*) [x', (*) [y', z']] .=. (*) [((*) [x', y']), z']) ∧
           (∀) "x" ((*) [one, x'] .=. x') ∧
           (∀) "x" ((*) [i [x'], x'] .=. one) ⇒
           (∀) "x" ((*) [x', i [x']] .=. one)
      x' = vt "x" :: TermType
      y' = vt "y" :: TermType
      z' = vt "z" :: TermType
      (*) = fApp (fromString "*")
      i = fApp (fromString "i")
      one = fApp (fromString "1") []
      expected =
          Set.fromList
                 [Success ((Map.fromList
                                   [( "_0",  (*) [one, vt' "_3"]),
                                    ( "_1",  (*) [fApp' "c_x" [],i [fApp' "c_x" []]]),
                                    ( "_2",  one),
                                    ( "_3",  (*) [fApp' "c_x" [],i [fApp' "c_x" []]]),
                                    ( "_4",  vt' "_8"),
                                    ( "_5",  (*) [one, vt' "_3"]),
                                    ( "_6",  one),
                                    ( "_7",  vt' "_11"),
                                    ( "_8",  vt' "_12"),
                                    ( "_9",  (*) [one, vt' "_3"]),
                                    ("_10", (*) [vt' "_13",(*) [vt' "_14", vt' "_15"]]),
                                    ("_11", (*) [(*) [vt' "_13", vt' "_14"], vt' "_15"]),
                                    ("_12", (*) [vt' "_19", vt' "_18"]),
                                    ("_13", vt' "_16"),
                                    ("_14", vt' "_21"),
                                    ("_15", (*) [vt' "_22", vt' "_23"]),
                                    ("_16", vt' "_20"),
                                    ("_17", (*) [vt' "_14", vt' "_15"]),
                                    ("_18", (*) [(*) [vt' "_21", vt' "_22"], vt' "_23"]),
                                    ("_19", vt' "_20"),
                                    ("_20", i [vt' "_28"]),
                                    ("_21", vt' "_28"),
                                    ("_22", fApp' "c_x" []),
                                    ("_23", i [fApp' "c_x" []]),
                                    ("_24", (*) [vt' "_13", vt' "_14"]),
                                    ("_25", (*) [vt' "_22", vt' "_23"]),
                                    ("_26", (*) [fApp' "c_x" [],i [fApp' "c_x" []]]),
                                    ("_27", one),
                                    ("_28", vt' "_30"),
                                    ("_29", (*) [vt' "_22", vt' "_23"]),
                                    ("_30", (*) [(*) [vt' "_21", vt' "_22"], vt' "_23"])],
                            0,31),13)]
      fApp' = fApp . fromString
      vt' = vt . fromString
