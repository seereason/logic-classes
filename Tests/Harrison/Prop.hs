{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Harrison.Prop
    ( tests
    ) where

import qualified Data.Set as Set
import Formulas (IsCombinable(..), (∨), (∧), true, false, atomic, (.~.), (¬))
import Lib ((|=>))
import Prelude hiding (negate)
import Prop (atoms, cnf', dnf, dual, eval, nnf, PFormula(Atom, Not, Imp, Iff, Or, And), Prop(..),
             psimplify, psubst, purednf, rawdnf, tautology, trivial, truthTable, TruthTable(TruthTable))
import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)

-- main = runTestTT tests

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Prop" $
        TestList [test01, test02, test03, test04, {-test05,-}
                  test06, test07, test08, test09, test10,
                  test11, test12, test13, test14, test15,
                  test16, test17, test18, test19, test20,
                  test21, test22, test23, test24, test25,
                  test26, test27, test28, test29, test30,
                  test31, test32, test33, test34, test35,
                  test36]

-- Variables for use in test cases

-- (p, q, r, s, t, u, v) = (Atom (P "p"), Atom (P "q"), Atom (P "r"), Atom (P "s"), Atom (P "t"), Atom (P "u"), Atom (P "v"))

test36 :: Test
test36 = TestCase $ assertEqual "show propositional formula 1" expected input
    where input = map show fms
          expected = ["((P \"p\") .&. (P \"q\")) .|. (P \"r\")",
                      "(P \"p\") .&. ((P \"q\") .|. (P \"r\"))",
                      "((P \"p\") .&. (P \"q\")) .|. (P \"r\")"]
          fms :: [PFormula Prop]
          fms = [p .&. q .|. r, p .&. (q .|. r), (p .&. q) .|. r]
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- ------------------------------------------------------------------------- 
-- Testing the parser and printer.                                           
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestCase $ assertEqual "Build Formula 1" expected input
    where input = (p .=>. q .<=>. r .&. s .|. (t .<=>. ((.~.) ((.~.) u)) .&. v))
          expected = (Iff
                      (Imp
                       (Atom (P {pname = "p"}))
                       (Atom (P {pname = "q"})))
                      (Or
                       (And (Atom (P {pname = "r"})) (Atom (P {pname = "s"})))
                       (Iff (Atom (P {pname = "t"}))
                        (And ({-Not-} ({-Not-} (Atom (P {pname = "u"})))) (Atom (P {pname = "v"}))))))
          (p, q, r, s, t, u, v) = (Atom (P "p"), Atom (P "q"), Atom (P "r"), Atom (P "s"), Atom (P "t"), Atom (P "u"), Atom (P "v"))

test02 :: Test
test02 = TestCase $ assertEqual "Build Formula 2" expected input
    where input = (Atom "fm" .&. Atom "fm")
          expected = (And (Atom "fm") (Atom "fm"))

test03 :: Test
test03 = TestCase $ assertEqual "Build Formula 3"
                                (Atom "fm" .|. Atom "fm" .&. Atom "fm")
                                (Or (Atom "fm") (And (Atom "fm") (Atom "fm")))

-- ------------------------------------------------------------------------- 
-- Example of use.                                                           
-- ------------------------------------------------------------------------- 

test04 :: Test
test04 = TestCase $ assertEqual "fixity tests" expected input
    where (input, expected) = unzip (map (\ (fm, flag) -> (eval fm (const False), flag)) pairs)
          pairs :: [(PFormula String, Bool)]
          pairs =
              [ ( true .&. false .=>. false .&. true,  True)
              , ( true .&. true  .=>. true  .&. false, False)
              , (   false ∧  true  ∨ true,             True)  -- "∧ binds more tightly than ∨"
              , (  (false ∧  true) ∨ true,             True)
              , (   false ∧ (true  ∨ true),            False)
              , (  (¬) true ∨ true,                    True)  -- "¬ binds more tightly than ∨"
              , (  (¬) (true ∨ true),                  False)
              ]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test06 :: Test
test06 = TestCase $ assertEqual "atoms test" (atoms $ p .&. q .|. s .=>. ((.~.) p) .|. (r .<=>. s)) (Set.fromList [P "p",P "q",P "r",P "s"])
    where (p, q, r, s) = (Atom (P "p"), Atom (P "q"), Atom (P "r"), Atom (P "s"))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test07 :: Test
test07 = TestCase $ assertEqual "truth table 1 (p. 36)" expected input
    where input = (truthTable $ p .&. q .=>. q .&. r)
          expected =
              (TruthTable
               [P "p", P "q", P "r"]
               [([False,False,False],True),
               ([False,False,True],True),
               ([False,True,False],True),
               ([False,True,True],True),
               ([True,False,False],True),
               ([True,False,True],True),
               ([True,True,False],False),
               ([True,True,True],True)])
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- ------------------------------------------------------------------------- 
-- Additional examples illustrating formula classes.                         
-- ------------------------------------------------------------------------- 

test08 :: Test
test08 = TestCase $
    assertEqual "truth table 2 (p. 39)"
                (truthTable $  ((p .=>. q) .=>. p) .=>. p)
                (TruthTable
                 [P "p", P "q"]
                 [([False,False],True),
                  ([False,True],True),
                  ([True,False],True),
                  ([True,True],True)])
        where (p, q) = (Atom (P "p"), Atom (P "q"))

test09 :: Test
test09 = TestCase $
    assertEqual "truth table 3 (p. 40)" expected input
        where input = (truthTable $ p .&. ((.~.) p))
              expected = (TruthTable
                          [P "p"]
                          [([False],False),
                          ([True],False)])
              p = Atom (P "p")

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test10 :: Test
test10 = TestCase $ assertEqual "tautology 1 (p. 41)" True (tautology $ p .|. ((.~.) p)) where p = Atom (P "p")
test11 :: Test
test11 = TestCase $ assertEqual "tautology 2 (p. 41)" False (tautology $ p .|. q .=>. p) where (p, q) = (Atom (P "p"), Atom (P "q"))
test12 :: Test
test12 = TestCase $ assertEqual "tautology 3 (p. 41)" False (tautology $ p .|. q .=>. q .|. (p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))
test13 :: Test
test13 = TestCase $ assertEqual "tautology 4 (p. 41)" True (tautology $ (p .|. q) .&. ((.~.)(p .&. q)) .=>. ((.~.)p .<=>. q)) where (p, q) = (Atom (P "p"), Atom (P "q"))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test14 :: Test
test14 =
    TestCase $ assertEqual "pSubst (p. 41)" expected input
        where expected = (p .&. q) .&. q .&. (p .&. q) .&. q
              input = psubst ((P "p") |=> (p .&. q)) (p .&. q .&. p .&. q)
              (p, q) = (Atom (P "p"), Atom (P "q"))

-- ------------------------------------------------------------------------- 
-- Surprising tautologies including Dijkstra's "Golden rule".                
-- ------------------------------------------------------------------------- 

test15 :: Test
test15 = TestCase $ assertEqual "tautology 5 (p. 43)" expected input
    where input = tautology $ (p .=>. q) .|. (q .=>. p)
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test16 :: Test
test16 = TestCase $ assertEqual "tautology 6 (p. 45)" expected input
    where input = tautology $ p .|. (q .<=>. r) .<=>. (p .|. q .<=>. p .|. r)
          expected = True
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))
test17 :: Test
test17 = TestCase $ assertEqual "Dijkstra's Golden Rule (p. 45)" expected input
    where input = tautology $ p .&. q .<=>. ((p .<=>. q) .<=>. p .|. q)
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test18 :: Test
test18 = TestCase $ assertEqual "Contraposition 1 (p. 46)" expected input
    where input = tautology $ (p .=>. q) .<=>. (((.~.)q) .=>. ((.~.)p))
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test19 :: Test
test19 = TestCase $ assertEqual "Contraposition 2 (p. 46)" expected input
    where input = tautology $ (p .=>. ((.~.)q)) .<=>. (q .=>. ((.~.)p))
          expected = True
          (p, q) = (Atom (P "p"), Atom (P "q"))
test20 :: Test
test20 = TestCase $ assertEqual "Contraposition 3 (p. 46)" expected input
    where input = tautology $ (p .=>. q) .<=>. (q .=>. p)
          expected = False
          (p, q) = (Atom (P "p"), Atom (P "q"))

-- ------------------------------------------------------------------------- 
-- Some logical equivalences allowing elimination of connectives.            
-- ------------------------------------------------------------------------- 

test21 :: Test
test21 = TestCase $ assertEqual "Equivalences (p. 47)" expected input
    where input =
              map tautology
              [ true .<=>. false .=>. false
              , ((.~.)p) .<=>. p .=>. false
              , p .&. q .<=>. (p .=>. q .=>. false) .=>. false
              , p .|. q .<=>. (p .=>. false) .=>. q
              , (p .<=>. q) .<=>. ((p .=>. q) .=>. (q .=>. p) .=>. false) .=>. false ]
          expected = [True, True, True, True, True]
          (p, q) = (Atom (P "p"), Atom (P "q"))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test22 :: Test
test22 = TestCase $ assertEqual "Dual (p. 49)" expected input
    where input = dual (Atom (P "p") .|. ((.~.) (Atom (P "p"))))
          expected = And (Atom (P {pname = "p"})) (Not (Atom (P {pname = "p"})))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test23 :: Test
test23 = TestCase $ assertEqual "psimplify 1 (p. 50)" expected input
    where input = psimplify $ (true .=>. (x .<=>. false)) .=>. ((.~.) (y .|. false .&. z))
          expected = ((.~.) x) .=>. ((.~.) y)
          x = Atom (P "x")
          y = Atom (P "y")
          z = Atom (P "z")

test24 :: Test
test24 = TestCase $ assertEqual "psimplify 2 (p. 51)" expected input
    where input = psimplify $ ((x .=>. y) .=>. true) .|. (.~.) false
          expected = true
          x = Atom (P "x")
          y = Atom (P "y")

-- ------------------------------------------------------------------------- 
-- Example of NNF function in action.                                        
-- ------------------------------------------------------------------------- 

test25 :: Test
test25 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = nnf $ (p .<=>. q) .<=>. ((.~.)(r .=>. s))
          expected = Or (And (Or (And p q) (And (Not p) (Not q)))
                        (And r (Not s)))
                        (And (Or (And p (Not q)) (And (Not p) q))
                             (Or (Not r) s))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
          s = Atom (P "s")

test26 :: Test
test26 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = tautology (Iff fm fm')
          expected = True
          fm' = nnf fm
          fm = (p .<=>. q) .<=>. ((.~.)(r .=>. s))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
          s = Atom (P "s")

-- ------------------------------------------------------------------------- 
-- Some tautologies remarked on.                                             
-- ------------------------------------------------------------------------- 

test27 :: Test
test27 = TestCase $ assertEqual "tautology 1 (p. 53)" expected input
    where input = tautology $ (p .=>. p') .&. (q .=>. q') .=>. (p .&. q .=>. p' .&. q')
          expected = True
          p = Atom (P "p")
          q = Atom (P "q")
          p' = Atom (P "p'")
          q' = Atom (P "q'")
test28 :: Test
test28 = TestCase $ assertEqual "nnf 1 (p. 53)" expected input
    where input = tautology $ (p .=>. p') .&. (q .=>. q') .=>. (p .|. q .=>. p' .|. q')
          expected = True
          p = Atom (P "p")
          q = Atom (P "q")
          p' = Atom (P "p'")
          q' = Atom (P "q'")

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test29 :: Test
test29 = TestCase $ assertEqual "dnf 1 (p. 56)" expected input
    where input = (dnf fm, truthTable fm)
          expected = (Or (And (Not r) p) (And r (And (Not p) q)),
                      (TruthTable
                       [P {pname = "p"}, P {pname = "q"}, P {pname = "r"}]
                       [([False,False,False],False),
                        ([False,False,True],False),
                        ([False,True,False],False),
                        ([False,True,True],True),
                        ([True,False,False],True),
                        ([True,False,True],False),
                        ([True,True,False],True),
                        ([True,True,True],False)]))
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

test30 :: Test
test30 = TestCase $ assertEqual "dnf 2 (p. 56)" expected input
    where input = dnf (p .&. q .&. r .&. s .&. t .&. u .|. u .&. v :: PFormula Prop)
          expected = (v .&. u) .|. (q .&. (r .&. (s .&. (t .&. ((u .&. p))))))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
          s = Atom (P "s")
          t = Atom (P "t")
          u = Atom (P "u")
          v = Atom (P "v")

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test31 :: Test
test31 = TestCase $ assertEqual "rawdnf (p. 58)" expected input
    where input = rawdnf $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = ((atomic (P "p")) .&. ((.~.)(atomic (P "p"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "p")))) .|.
                     ((atomic (P "p")) .&. ((.~.)(atomic (P "r"))) .|.
                      ((atomic (P "q")) .&. (atomic (P "r"))) .&. ((.~.)(atomic (P "r"))))
          (p, q, r) = (Atom (P "p"), Atom (P "q"), Atom (P "r"))

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test32 :: Test
test32 = TestCase $ assertEqual "purednf (p. 58)" expected input
    where input = purednf id $ (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          expected = Set.fromList [Set.fromList [p,Not p],
                                   Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p],
                                   Set.fromList [q,r,Not r]]
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test33 :: Test
test33 = TestCase $ assertEqual "trivial" expected input
    where input = Set.filter (not . trivial) (purednf id fm)
          expected = Set.fromList [Set.fromList [p,Not r],
                                   Set.fromList [q,r,Not p]]
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test34 :: Test
test34 = TestCase $ assertEqual "dnf" expected input
    where input = (dnf fm, tautology (Iff fm (dnf fm)))
          expected = (Or (And (Not r) p) (And r (And (Not p) q)), True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test35 :: Test
test35 = TestCase $ assertEqual "cnf" expected input
    where input = (cnf' fm, tautology (Iff fm (cnf' fm)))
          -- Fully parenthesized
          -- expected = (((atomic (P "r")) .|. (atomic (P "p"))) .&. (((((.~.)(atomic (P "r")))) .|. (((.~.)(atomic (P "p"))))) .&. ((atomic (P "q")) .|. (atomic (P "p")))),True)
          -- Edited
          expected = (   ((atomic (P "r"))           .|. (atomic (P "p")))          .&.
                      (  (((.~.)(atomic (P "r")))   .|. ((.~.)(atomic (P "p"))))    .&.
                         ((atomic (P "q"))          .|. (atomic (P "p")))            ),
                      True)
          -- expected = (And (Or q p) (And (Or r p) (Or (Not r) (Not p))),True)
          -- expected = (F, True)
          -- expected = (((atomic (P "r")) .|. (atomic (P "p"))) .&. (((((.~.)(atomic (P "r"))))) .|. ((((.~.)(atomic (P "p"))))) .&. (atomic (P "q")) .|. (atomic (P "p"))),True)
          fm = (p .|. q .&. r) .&. (((.~.)p) .|. ((.~.)r))
          p = Atom (P "p")
          q = Atom (P "q")
          r = Atom (P "r")
