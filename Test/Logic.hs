{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-missing-signatures -fno-warn-orphans #-}
module Test.Logic (tests) where

import Data.List (intercalate)
import qualified Data.Set as Set
import Data.String (IsString(fromString))
import Logic.CNF
import Logic.Instances.Parameterized
import Logic.Instances.PropLogic
import Logic.Logic
import Logic.Predicate
import PropLogic
import qualified TextDisplay as TD
import Test.HUnit

instance Skolem V String where
    skolem (V s) = "Sk(" ++ s ++ ")"

instance Show (Formula String String) where
    show = showForm

tests :: [Test]
tests = precTests ++ cnfTests ++ theoremTests

formCase :: PredicateLogic (Formula String String) (Term String) V String String =>
            String -> Formula String String -> Formula String String -> Test
formCase s expected input = TestCase (assertEqual s expected input)

precTests :: [Test]
precTests =
    [ formCase "prec test 1"
               -- Note that the result of cnf is a conjunction of disjunctions, which
               -- will not group properly without parentheses.
               ((a .&. b) .|. c)
               (a .&. b .|. c)
      -- You can't apply .~. without parens:
      -- :type (.~. a)   -> (FormulaPF -> t) -> t
      -- :type ((.~.) a) -> FormulaPF
    , formCase "prec test 2"
               (((.~.) a) .&. b)
               ((.~.) a .&. b)
    -- I switched the precedence of .&. and .|. from infixl to infixr to get
    -- some of the test cases to match the answers given on the miami.edu site,
    -- but maybe I should switch them back and adjust the answer given in the
    -- test case.
    , formCase "prec test 3"
               ((a .&. b) .&. c) -- infixl, with infixr we get (a .&. (b .&. c))
               (a .&. b .&. c)
    , TestCase (assertEqual "Find a free variable"
                (freeVars (for_all [x'] (x .=. y) :: Formula String String))
                (Set.singleton y'))
    , TestCase (assertEqual "Substitute a variable"
                (map (substitute "z")
                         [ for_all [x'] (x .=. y) :: Formula String String
                         , for_all [y'] (x .=. y) :: Formula String String ])
                [ for_all [x'] (x .=. z) :: Formula String String
                , for_all [y'] (z .=. y) :: Formula String String ])
    ]
    where
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

cnfTests :: [Test]
cnfTests = [test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11, test12, test9a,
            moveQuantifiersOut1, skolemize1]

p vs = pApp "p" vs
q vs = pApp "q" vs
r vs = pApp "r" vs
s vs = pApp "s" vs
x' = V "x"
y' = V "y"
z' = V "z"
u' = V "u"
v' = V "v"
w' = V "w"
x = var x'
y = var y'
z = var z'
u = var u'
v = var v'
w = var w'

-- Test cases from http://www.cs.miami.edu/~geoff/Courses/CS63S-09S/Content/FOFToCNF.shtml
-- 
-- :load SeeReason.Types.Atomic
-- :m +Logic.Class
-- :set -XOverloadedStrings

test1 =
    formCase "cnf test 1"
              ((((.~.) (taller y xy)) .|. (wise y)) .&. ((.~.) (wise xy) .|. (wise y)))
              (cnf (for_all [y'] (for_all [x'] (taller y x .|. wise x) .=>. wise y)))
        where
          xy = fApp (fromString "Sk(x)") [y]
          taller a b = pApp "taller" [a, b]
          wise a = pApp "wise" [a]

test2 = formCase "cnf test 2"
                  (((.~.) (pApp "s" [x])) .|. ((.~.) (pApp "q" [x])))
                  (cnf ((.~.) (exists [x'] (pApp "s" [x] .&. pApp "q" [x]))))
test3 = formCase "cnf test 3"
                  (((.~.) (p [x])) .|. ((q [x]) .|. (r [x])))
                  (cnf (for_all [x'] (p [x] .=>. (q [x] .|. r [x]))))

test4 = formCase "cnf test 4"
                  (p [x] .&. (.~.) (q [y]))
                  (cnf ((.~.) (exists [x'] (p [x] .=>. exists [x'] (q [x])))))

test5 = formCase "cnf test 5"
                  ((((.~.) (q [x])) .|. s [x]) .&. (((.~.) (r [x])) .|. s [x]))
                  (cnf (for_all [x'] (q [x] .|. r [x] .=>. s [x])))

test6 = formCase "cnf test 6"
                  ((.~.) p .|. f skX)
                  (cnf (exists [x'] (p .=>. f x)))
    where
      skX = fApp "Sk(x)" []
      f x = pApp "f" [x]
      p = pApp "p" []

test7 = formCase "cnf test 7"
                  -- This is what was given by the source
                  -- (((.~.) p) .|. f skX .&. p .|. ((.~.) (f skX)))
                  -- This is what we are currently getting from our
                  -- code, which is different but still may be correct.  However, we may
                  ((((.~.) p) .|. (f skX)) .&. (((.~.) (f skX)) .|. p))
                  -- (((p []) .|. (p [])) .&. ((((.~.) (f [x])) .|. ((.~.) (f [x]))) .|. (p [])))
                  -- p
                  (cnf (exists [x'] (p .<=>. f x)))
    where
      skX = fApp "Sk(x)" []
      f x = pApp "f" [x]
      p = pApp "p" []

test8 = formCase "cnf test 8"
                  -- Original
               {- (((.~.) (f [x, yOfZ])) .|. f [x, z] .&.
                   ((.~.) (f [x, yOfZ])) .|. ((.~.) (f [x, x])) .&.
                   ((.~.) (f [x, z])) .|. f [x, x] .|. f [x, yOfZ]) -}

                  (((((.~.) (f [x, yOfZ])) .|. (f [x, z])) .&.
                    (((.~.) (f [x, yOfZ])) .|. ((.~.) (f [x, x])))) .&.
                   ((((.~.) (f [x, z])) .|. (f [x, x])) .|. (f [x, yOfZ])))

                  (cnf (for_all [z'] (exists [y'] (for_all [x'] (f [x, y] .<=>. (f [x, z] .&. ((.~.) (f [x, x]))))))))
    where
      (x', y', z') = (V "x", V "y", V "z")
      (x, y, z) = (var x', var y', var z')
      yOfZ = fApp "Sk(y)" [z]
      f vs = pApp "f" vs

test9 =
    formCase "cnf test 9"
             (((((.~.) (q [x,y])) .|. ((((.~.) (f [z,x])) .|. ((f [z,y]))))) .&.
               ((((.~.) (q [x,y])) .|. ((((.~.) (f [z,y])) .|. ((f [z,x]))))))) .&.
              ((((((f [fApp ("Sk(x1)") [x,y,z],x]) .|. ((f [fApp ("Sk(x1)") [x,y,z],y]))) .|. ((q [x,y]))) .&.
                 (((((.~.) (f [fApp ("Sk(x1)") [x,y,z],y])) .|. ((f [fApp ("Sk(x1)") [x,y,z],y]))) .|. ((q [x,y]))))) .&.
                (((((f [fApp ("Sk(x1)") [x,y,z],x]) .|. (((.~.) (f [fApp ("Sk(x1)") [x,y,z],x])))) .|. ((q [x,y]))) .&.
                  (((((.~.) (f [fApp ("Sk(x1)") [x,y,z],y])) .|. (((.~.) (f [fApp ("Sk(x1)") [x,y,z],x])))) .|. ((q [x,y])))))))))
             (cnf (for_all [x'] (for_all [y'] (q [x, y] .<=>. for_all [z'] (f [z, x] .<=>. f [z, y])))))
    where
      f = pApp "f"
      q = pApp "q"
      -- skZ = fApp "Sk(z)"
      (x', y', z') = (V "x", V "y", V "z")
      (x, y, z) = (var x', var y', var z')

-- |Here is an example of automatic conversion from a PredicateLogic
-- instance to a PropositionalLogic instance.  The result is PropForm
-- a where a is the original type, but the a values will always be
-- "atomic" formulas, never the operators which can be converted into
-- the corresponding operator of a PropositionalLogic instance.
test9a = TestCase 
           (assertEqual "convert to PropLogic"
            (Just (CJ [DJ [N (A (q [x,y])),N (A (f [z,x])),A (f [z,y])],
                       DJ [N (A (q [x,y])),N (A (f [z,y])),A (f [z,x])],
                       DJ [A (f [fApp ("Sk(x1)") [x,y,z],x]),A (f [fApp ("Sk(x1)") [x,y,z],y]),A (q [x,y])],
                       DJ [N (A (f [fApp ("Sk(x1)") [x,y,z],y])),A (f [fApp ("Sk(x1)") [x,y,z],y]),A (q [x,y])],
                       DJ [A (f [fApp ("Sk(x1)") [x,y,z],x]),N (A (f [fApp ("Sk(x1)") [x,y,z],x])),A (q [x,y])],
                       DJ [N (A (f [fApp ("Sk(x1)") [x,y,z],y])),N (A (f [fApp ("Sk(x1)") [x,y,z],x])),A (q [x,y])]]))
            ((toPropositional convertA (cnf (for_all [x'] (for_all [y'] (q [x, y] .<=>. for_all [z'] (f [z, x] .<=>. f [z, y])))))) >>=
             return . flatten :: Maybe (PropForm (Formula String String))))
    where
      f = pApp "f"
      q = pApp "q"
      convertA = Just . A

test10 = formCase "cnf test 10"
                  (((q [skY [x],skZ [x],skT [x]]) .|. ((p [x,skY [x]]))) .&. ((((.~.) (r [skY [x]])) .|. ((p [x,skY [x]])))))
                  (cnf (for_all [x'] (exists [y'] ((p [x, y] .<=. for_all [x'] (exists [t'] (q [y, x, t]) .=>. r [y]))))))
    where
      t' = V "t"
      t = var t'
      p = pApp "p"
      q = pApp "q"
      r = pApp "r"
      skY = fApp "Sk(y)"
      skZ = fApp "Sk(z)"
      skT = fApp "Sk(t)"

test11 = formCase "cnf test 11"
                  -- This one didn't come with a solution - here's ours
                  ((((.~.) (p [x,z])) .|. ((.~.) (q [x,skY [x,z]]))) .&. (((.~.) (p [x,z])) .|. (r [skY [x,z],z])))
                  (cnf (for_all [x'] (for_all [z'] (p [x, z] .=>. exists [y'] ((.~.) (q [x, y] .|. ((.~.) (r [y, z]))))))))
    where
      p = pApp "p"
      q = pApp "q"
      r = pApp "r"
      skY = fApp "Sk(y)"

test12 = formCase "cnf test 12"
                  (((p.|.(r.|.s)).&.(((.~.) q).|.(r.|.s))).&.((p.|.(r.|.t)).&.(((.~.) q).|.(r.|.t))))
                  (cnf ((p .=>. q) .=>. (((.~.) r) .=>. (s .&. t))))
    where
      [p, q, r, s, t] = map (\ s -> pApp s []) ["p", "q", "r", "s", "t"]

moveQuantifiersOut1 =
    formCase "moveQuantifiersOut1"
             (for_all [y'] (pApp (fromString "p") [y] .&. (pApp (fromString "q") [x])))
             (moveQuantifiersOut (for_all [x'] (pApp (fromString "p") [x]) .&. (pApp (fromString "q") [x])))

skolemize1 :: Test
skolemize1 =
    formCase "skolemize1" expected formula
    where
      expected :: Formula String String
      expected = pApp "P" [fApp ("Sk(x)") [], y, z, fApp ("Sk(u)") [y, z], v, fApp "Sk(w)" [y, z, v]]
      formula :: Formula String String
      formula = (skolemize [] (exists [x'] (for_all [y', z'] (exists [u'] (for_all [v'] (exists [w'] (pApp "P" [x, y, z, u, v, w])))))))

theoremTests = [theorem1 {-, theorem1a, theorem1b, theorem1c, theorem1d, theorem2-}]

theorem1 =
    TestCase (assertEqual "theorm test 1"
              (Just True)
              (theorem (for_all [x'] (((pApp "S" [x] .=>. pApp "H" [x]) .&.
                                       (pApp "H" [x] .=>. pApp "M" [x])) .=>.
                                      (pApp "S" [x] .=>. pApp "M" [x])))))

instance TD.Display (Formula String String) where
    textFrame x = [quickShow x]
        where
          quickShow =
              foldF (\ _ -> error "Expecting atoms")
                    (\ _ _ _ -> error "Expecting atoms")
                    (\ _ _ _ -> error "Expecting atoms")
                    (\ t1 op t2 -> quickShowTerm t1 ++ quickShowOp op ++ quickShowTerm t2)
                    (\ p ts -> quickShowPred p ++ quickShowTerms ts)
          quickShowTerm (Var v) = quickShowVar v
          quickShowTerm (FunApp fn ts) = quickShowFn fn ++ quickShowTerms ts
          quickShowTerms xs = "(" ++ intercalate "," (map quickShowTerm xs) ++ ")"
          quickShowVar (V s) = s
          quickShowPred s = s
          quickShowFn s = s
          quickShowOp (:=:) = "="
          quickShowOp (:!=:) = "!="

{-
-- Truth table tests, find a more reasonable result value than [String].

(theorem1a, theorem1b, theorem1c, theorem1d) =
    ( TestCase (assertEqual "truth table 1"
                (Just ["foo"])
                (prepare (for_all [x'] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))) >>=
                 return . TD.textFrame . truthTable))
    , TestCase (assertEqual "truth table 2"
                (Just ["foo"])
                (prepare (exists [x'] ((s [x] .=>. h [x]) .&. (h [x] .=>. m [x]) .&. s [x] .&. ((.~.) (m [x])))) >>=
                 return . TD.textFrame . truthTable))
    , TestCase (assertEqual "truth table 3"
                (Just ["foo"])
                (prepare (exists [x'] ((s [x] .=>. h [x]) .&. (h [x] .=>. m [x]) .&. s [x] .&. m [x])) >>=
                 return . TD.textFrame . truthTable))
    , TestCase (assertEqual "truth table 4"
                (Just ["foo"])
                (prepare (for_all [x'] (s [x] .=>. h [x]) .&. for_all [x'] (h [x] .=>. m [x]) .&. exists [x'] (s [x]) .&. exists [x'] (((.~.) (m [x])))) >>=
                 return . TD.textFrame . truthTable)) )
    where s = pApp "S"
          h = pApp "H"
          m = pApp "M"

theorem2 =
    TestCase (assertEqual "theorm test 2"
              (Just True)
              (theorem ((.~.) ((for_all [x'] (((pApp "S" [x] .=>. pApp "H" [x]) .&.
                                               (pApp "H" [x] .=>. pApp "M" [x]))) .&.
                                exists [x'] (pApp "S" [x] .&. ((.~.) (pApp "M" [x]))))))))
-}

type FormulaPF = Formula String String
type F = PropForm FormulaPF

-- |If the negation of a formula is satisfiable, then the formula was
-- not a tautology, which is to say, not a theorm.
-- theorem :: PredicateLogic formula atom term v p f => formula -> Maybe Bool
theorem :: FormulaPF -> Maybe Bool
theorem formula = prepare ((.~.) formula) >>= return . not . satisfiable

-- |Prepare ta formula to be passed to the satisfiability function.
prepare :: FormulaPF -> Maybe F
prepare formula = (toPropositional convertA . cnf $ formula) {- >>= return . flatten -}

convertA = Just . A
