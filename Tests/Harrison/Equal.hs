{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall #-}
module Harrison.Equal where

-- =========================================================================
-- First order logic with equality.
--
-- Copyright (co) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)
-- =========================================================================

import Common (render)
import Control.Applicative.Error (Failing(..))
import Data.List as List
import Data.Map as Map
import Data.Set as Set
import Data.String (IsString(fromString))
import Equal (equalitize, function_congruence)
import FOL ((.=.), (∃), (∀), IsTerm(..), pApp, Predicate, V)
import Formulas (IsCombinable(..), (∧), (⇒))
import Meson (meson)
import Prelude hiding ((*))
import Skolem (HasSkolem(..), MyTerm, MyFormula, runSkolem)
import Tableaux (Depth(Depth))
import Test.HUnit

-- type TF = TestFormula (Formula FOL) FOL MyTerm String String Function
-- type TFE = TestFormulaEq (MyFormula) FOLEQ MyTerm String String Function

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Equal" $ TestList [test01, test02, test03, test04]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestCase $ assertEqual "function_congruence" expected input
    where input = List.map function_congruence [(fromString "f", 3 :: Int), (fromString "+",2)]
          expected :: [Set.Set (MyFormula)]
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

test :: (Show a, Eq a) => String -> a -> a -> Test
test label expected input = TestLabel label $ TestCase $ assertEqual label expected input

test02 :: Test
test02 = TestCase $ assertEqual "equalitize 1 (p. 241)" (expected, expectedProof) input
    where input = (render ewd, runSkolem (meson (Just (Depth 10)) ewd))
          ewd = equalitize fm :: MyFormula
          fm :: MyFormula
          fm = ((∀) "x" (fx ⇒ gx)) ∧
               ((∃) "x" fx) ∧
               ((∀) "x" ((∀) "y" (gx ∧ gy ⇒ x .=. y))) ⇒
               ((∀) "y" (gy ⇒ fy))
          fx = pApp' "f" [x]
          gx = pApp' "g" [x]
          fy = pApp' "f" [y]
          gy = pApp' "g" [y]
          x = vt "x"
          y = vt "y"
          z = vt "z"
          x1 = vt "x1"
          y1 = vt "y1"
          fx1 = pApp' "f" [x1]
          gx1 = pApp' "g" [x1]
          fy1 = pApp' "f" [y1]
          gy1 = pApp' "g" [y1]
          -- y1 = fromString "y1"
          -- z = fromString "z"
          expected = render $
              ((∀) "x" (x .=. x)) .&.
              ((∀) "x" ((∀) "y" ((∀) "z" (x .=. y .&. x .=. z .=>. y .=. z)))) .&.
              ((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. fx1 .=>. fy1))) .&.
              ((∀) "x1" ((∀) "y1" (x1 .=. y1 .=>. gx1 .=>. gy1))) .=>.
              ((∀) "x" (fx .=>. gx)) .&.
              ((∃) "x" (fx)) .&.
              ((∀) "x" ((∀) "y" (gx .&. gy .=>. x .=. y))) .=>.
              ((∀) "y" (gy .=>. fy))
{-
          -- I don't yet know if this is right.  Almost certainly not.
          expectedProof = Set.fromList [Success ((Map.fromList [("_0",vt "_1")],0,2),1),
                                        Success ((Map.fromList [("_0",vt "_2"),("_1",vt "_2")],0,3),1),
                                        Success ((Map.fromList [("_0",fApp (Skolem 1) [] :: MyTerm)],0,1),1),
                                        Success ((Map.fromList [("_0",fApp (Skolem 2) [] :: MyTerm)],0,1),1)]

          expected = ("<<(forall x. x = x) /\ " ++
                      "    (forall x y z. x = y /\ x = z ==> y = z) /\ " ++
                      "    (forall x1 y1. x1 = y1 ==> f(x1) ==> f(y1)) /\ " ++
                      "    (forall x1 y1. x1 = y1 ==> g(x1) ==> g(y1)) ==> " ++
                      "    (forall x. f(x) ==> g(x)) /\ " ++
                      "    (exists x. f(x)) /\ (forall x y. g(x) /\ g(y) ==> x = y) ==> " ++
                      "    (forall y. g(y) ==> f(y))>> ")
-}
          expectedProof =
              Set.fromList [Success ((Map.fromList [(fromString "_0",vt "_2"),
                                                    (fromString "_1",fApp (toSkolem "y") []),
                                                    (fromString "_2",vt "_4"),
                                                    (fromString "_3",fApp (toSkolem "y") []),
                                                    (fromString "_4",fApp (toSkolem "x") [])],0,5),Depth 6)]
{-
          expectedProof =
              Set.singleton (Success ((Map.fromList [(fromString "_0",vt' "_2"),
                                                     (fromString "_1",fApp (toSkolem "x") []),
                                                     (fromString "_2",vt' "_4"),
                                                     (fromString "_3",fApp (toSkolem "x") []),
                                                     (fromString "_4",fApp (toSkolem "x") []),
                                                     (fromString "_5",fApp (toSkolem "x") [])], 0, 6), 5))
          fApp' :: String -> [term] -> term
          fApp' s ts = fApp (fromString s) ts
          for_all' s = for_all (fromString s)
          exists' s = exists (fromString s)
-}
          pApp' :: String -> [MyTerm] -> MyFormula
          pApp' s ts = pApp (fromString s :: Predicate) ts
          --vt' :: String -> MyTerm
          --vt' s = vt (fromString s)

-- ------------------------------------------------------------------------- 
-- Wishnu Prasetya's example (even nicer with an "exists unique" primitive). 
-- ------------------------------------------------------------------------- 

wishnu :: MyFormula
wishnu = ((∃) ("x") ((x .=. f[g[x]]) ∧ (∀) ("x'") ((x' .=. f[g[x']]) ⇒ (x .=. x')))) .<=>.
         ((∃) ("y") ((y .=. g[f[y]]) ∧ (∀) ("y'") ((y' .=. g[f[y']]) ⇒ (y .=. y'))))
    where
      x = vt "x"
      y = vt "y"
      x' = vt "x'"
      y' = vt "y"
      f terms = fApp (fromString "f") terms
      g terms = fApp (fromString "g") terms

test03 :: Test
test03 = TestLabel "equalitize 2" $ TestCase $ assertEqual "equalitize 2 (p. 241)" (render expected, expectedProof) input
    where -- This depth is not sufficient to finish. It shoudl work with 16, but that takes a long time.
          input = (render (equalitize wishnu), runSkolem (meson (Just (Depth 16)) wishnu))
          x = vt "x" :: MyTerm
          x1 = vt "x1"
          y = vt "y"
          y1 = vt "y1"
          z = vt "z"
          x' = vt "x'"
          y' = vt "y"
          f terms = fApp (fromString "f") terms
          g terms = fApp (fromString "g") terms
          expected :: MyFormula
          expected =
                     ((∀) "x" (x .=. x)) .&.
                     ((∀) "x" . (∀) "y" . (∀) "z" $ (x .=. y .&. x .=. z .=>. y .=. z)) .&.
                     ((∀) "x1" . (∀) "y1" $ (x1 .=. y1 .=>. f[x1] .=. f[y1])) .&.
                     ((∀) "x1" . (∀) "y1" $ (x1 .=. y1 .=>. g[x1] .=. g[y1])) .=>.
                     (((∃) "x" $ x .=. f[g[x]] .&. ((∀) "x'" $ (x' .=. f[g[x']] .=>. x .=. x'))) .<=>.
                      ((∃) "y" $ y .=. g[f[y]] .&. ((∀) "y'" $ (y' .=. g[f[y']] .=>. y .=. y'))))
          expectedProof =
              Set.fromList [Failure ["Not sure what we git here if this finishes"]]
{-
              Set.fromList [Success ((Map.fromList [("_0",vt "_1")],0,2 :: Map.Map String MyTerm),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_1",fApp "f" [fApp "g" [vt "_0"]])],0,2),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_1",fApp "g" [fApp "f" [vt "_0"]])],0,2),1),
                            Success ((Map.fromList [("_0",vt "_1"),("_2",fApp (fromSkolem 2) [vt "_0"])],0,3),1),
                            Success ((Map.fromList [("_0",vt "_2"),("_1",vt "_2")],0,3),1)] -}

-- -------------------------------------------------------------------------
-- More challenging equational problems. (Size 18, 61814 seconds.)
-- -------------------------------------------------------------------------

test04 :: Test
test04 = TestCase $ assertEqual "equalitize 3 (p. 248)" (render expected, expectedProof) input
    where
      input = (render (equalitize fm), runSkolem (meson (Just (Depth 20)) . equalitize $ fm))
      fm :: MyFormula
      fm = ((∀) "x" . (∀) "y" . (∀) "z") ((*) [x', (*) [y', z']] .=. (*) [((*) [x', y']), z']) ∧
           (∀) "x" ((*) [one, x'] .=. x') ∧
           (∀) "x" ((*) [i [x'], x'] .=. one) ⇒
           (∀) "x" ((*) [x', i [x']] .=. one)
      x' = vt "x" :: MyTerm
      y' = vt "y" :: MyTerm
      z' = vt "z" :: MyTerm
      (*) = fApp (fromString "*")
      i = fApp (fromString "i")
      one = fApp (fromString "1") []
      expected :: MyFormula
      expected =
          ((∀) "x" ((vt "x") .=. (vt "x")) .&.
           ((∀) "x" ((∀) "y" ((∀) "z" ((((vt "x") .=. (vt "y")) .&. ((vt "x") .=. (vt "z"))) .=>. ((vt "y") .=. (vt "z"))))) .&.
            ((∀) "x1" ((∀) "x2" ((∀) "y1" ((∀) "y2" ((((vt "x1") .=. (vt "y1")) .&. ((vt "x2") .=. (vt "y2"))) .=>.
                                                                     ((fApp "*" [vt "x1",vt "x2"]) .=. (fApp "*" [vt "y1",vt "y2"])))))) .&.
             (∀) "x1" ((∀) "y1" (((vt "x1") .=. (vt "y1")) .=>. ((fApp "i" [vt "x1"]) .=. (fApp "i" [vt "y1"]))))))) .=>.
          ((((∀) "x" ((∀) "y" ((∀) "z" ((fApp "*" [vt "x",fApp "*" [vt "y",vt "z"]]) .=. (fApp "*" [fApp "*" [vt "x",vt "y"],vt "z"])))) .&.
             (∀) "x" ((fApp "*" [fApp "1" [],vt "x"]) .=. (vt "x"))) .&.
            (∀) "x" ((fApp "*" [fApp "i" [vt "x"],vt "x"]) .=. (fApp "1" []))) .=>.
           (∀) "x" ((fApp "*" [vt "x",fApp "i" [vt "x"]]) .=. (fApp "1" [])))
      expectedProof :: Set.Set (Failing ((Map.Map V MyTerm, Int, Int), Depth))
      expectedProof =
          Set.fromList
                 [Success ((Map.fromList
                                   [( "_0",  (*) [one, vt' "_3"]),
                                    ( "_1",  (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
                                    ( "_2",  one),
                                    ( "_3",  (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
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
                                    ("_22", fApp (toSkolem "x") []),
                                    ("_23", i [fApp (toSkolem "x") []]),
                                    ("_24", (*) [vt' "_13", vt' "_14"]),
                                    ("_25", (*) [vt' "_22", vt' "_23"]),
                                    ("_26", (*) [fApp (toSkolem "x") [],i [fApp (toSkolem "x") []]]),
                                    ("_27", one),
                                    ("_28", vt' "_30"),
                                    ("_29", (*) [vt' "_22", vt' "_23"]),
                                    ("_30", (*) [(*) [vt' "_21", vt' "_22"], vt' "_23"])],
                            0,31),Depth 13)]
      vt' = vt . fromString
