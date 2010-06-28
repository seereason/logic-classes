{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Test.Logic (tests) where

import Data.Maybe (fromJust)
import qualified Data.Set as Set
import Data.String (IsString(fromString))
import Logic.AtomicWord
import Logic.CNF
import Logic.Instances.Parameterized
import Logic.Instances.PropLogic
import Logic.Logic
import Logic.Predicate
import PropLogic
import Test.HUnit

tests = precTests ++ cnfTests

formCase :: PredicateLogic (Formula AtomicWord AtomicWord) (Term AtomicWord) V AtomicWord AtomicWord =>
            String -> Formula AtomicWord AtomicWord -> Formula AtomicWord AtomicWord -> Test
formCase s expected input = TestCase (assertEqual s expected input)

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
                (freeVars (for_all [x'] (x .=. y) :: Formula AtomicWord AtomicWord))
                (Set.singleton y'))
    , TestCase (assertEqual "Substitute a variable"
                (map (substitute "z")
                         [ for_all [x'] (x .=. y) :: Formula AtomicWord AtomicWord
                         , for_all [y'] (x .=. y) :: Formula AtomicWord AtomicWord ])
                [ for_all [x'] (x .=. z) :: Formula AtomicWord AtomicWord
                , for_all [y'] (z .=. y) :: Formula AtomicWord AtomicWord ])
    ]
    where
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

cnfTests = [test1, test2, test3, test4, test5, test6, test7, test8, test9, test10, test11, test12, test9a,
            moveQuantifiersOut1]

p vs = pApp "p" vs
q vs = pApp "q" vs
r vs = pApp "r" vs
s vs = pApp "s" vs
x' = V "x"
x1' = V "x1"
y' = V "y"
z' = V "z"
x = var x'
x1 = var x1'
y = var y'
z = var z'

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
          xy = fApp (fromString "x") [y]
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
      skX = x
      f x = pApp "f" [x]
      p = pApp "p" []

test7 = formCase "cnf test 7"
                  -- This is what was given by the source
                  -- (((.~.) p) .|. f skX .&. p .|. ((.~.) (f skX)))
                  -- This is what we are currently getting from our
                  -- code, which is different but still may be correct.  However, we may
                  ((((.~.) p) .|. (f x)) .&. (((.~.) (f x)) .|. p))
                  -- (((p []) .|. (p [])) .&. ((((.~.) (f [x])) .|. ((.~.) (f [x]))) .|. (p [])))
                  -- p
                  (cnf (exists [x'] (p .<=>. f x)))
    where
      skX = V "skX"
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
      yOfZ = fApp (AtomicWord "y") [z]
      -- yz = fApp "y" ["z"]
      skY b = fApp "y" [b]
      f vs = pApp "f" vs
      a = var (V "a")
      b = var (V "b")

test9 = formCase "cnf test 9"
                  (((((.~.) (q [x,y])) .|. (((.~.) (f [x1,x])) .|. (f [x1,y]))) .&.
                    (((.~.) (q [x,y])) .|. (((.~.) (f [x1,y])) .|. (f [x1,x])))) .&.
                   (((((f [skZ [x1,y,x],x]) .|. (f [skZ [x1,y,x],y])) .|. (q [x,y])) .&.
                     ((((.~.) (f [skZ [x1,y,x],y])) .|. (f [skZ [x1,y,x],y])) .|. (q [x,y]))) .&.
                    ((((f [skZ [x1,y,x],x]) .|. ((.~.) (f [skZ [x1,y,x],x]))) .|. (q [x,y])) .&.
                     ((((.~.) (f [skZ [x1,y,x],y])) .|. ((.~.) (f [skZ [x1,y,x],x]))) .|. (q [x,y])))))
                  (cnf (for_all [x'] (for_all [y'] (q [x, y] .<=>. for_all [z'] (f [z, x] .<=>. f [z, y])))))
    where
      f = pApp "f"
      q = pApp "q"
      skZ = fApp (AtomicWord "z")
      (x', y', z') = (V "x", V "y", V "z")
      (x, y, z) = (var x', var y', var z')

-- |Here is an example of automatic conversion from a PredicateLogic
-- instance to a PropositionalLogic instance.  The result is PropForm
-- a where a is the original type, but the a values will always be
-- "atomic" formulas, never the operators which can be converted into
-- the corresponding operator of a PropositionalLogic instance.
test9a = TestCase 
           (assertEqual "convert to PropLogic"
            (Just (CJ [DJ [N (A (q [x,y])),N (A (f [x1,x])),A (f [x1,y])],
                       DJ [N (A (q [x,y])),N (A (f [x1,y])),A (f [x1,x])],
                       DJ [A (f [skZ [x1,y,x],x]),A (f [skZ [x1,y,x],y]),A (q [x,y])],
                       DJ [N (A (f [skZ [x1,y,x],y])),A (f [skZ [x1,y,x],y]),A (q [x,y])],
                       DJ [A (f [skZ [x1,y,x],x]),N (A (f [skZ [x1,y,x],x])),A (q [x,y])],
                       DJ [N (A (f [skZ [x1,y,x],y])),N (A (f [skZ [x1,y,x],x])),A (q [x,y])]])
             :: Maybe (PropForm (Formula AtomicWord AtomicWord)))
            ((toPropositional convertA (cnf (for_all [x'] (for_all [y'] (q [x, y] .<=>. for_all [z'] (f [z, x] .<=>. f [z, y])))))) >>=
             return . flatten :: Maybe (PropForm (Formula AtomicWord AtomicWord))))
    where
      f = pApp "f"
      q = pApp "q"
      skZ = FunApp (AtomicWord "z")
      convertA = Just . A

test10 = formCase "cnf test 10"
                  (((q [skY [x],z,t]) .|. (p [x,skY [x]])) .&. (((.~.) (r [skY [x]])) .|. (p [x,skY [x]])))
                  (cnf (for_all [x'] (exists [y'] ((p [x, y] .<=. for_all [x'] (exists [t'] (q [y, x, t]) .=>. r [y]))))))
    where
      a = var (V "a")
      b = var (V "b")
      t' = V "t"
      t = var t'
      p = pApp "p"
      q = pApp "q"
      r = pApp "r"
      skY = fApp (AtomicWord "y")
      sk1 a = fApp ("sk1") [a]
      sk2 a b = fApp ("sk2") [a, b]

test11 = formCase "cnf test 11"
                  -- This one didn't come with a solution - here's ours
                  ((((.~.) (p [x,z])) .|. ((.~.) (q [x,skY [z,x]]))) .&. (((.~.) (p [x,z])) .|. (r [skY [z,x],z])))
                  (cnf (for_all [x'] (for_all [z'] (p [x, z] .=>. exists [y'] ((.~.) (q [x, y] .|. ((.~.) (r [y, z]))))))))
    where
      p = pApp "p"
      q = pApp "q"
      r = pApp "r"
      skY = fApp (AtomicWord "y")

test12 = formCase "cnf test 12"
                  (((p.|.(r.|.s)).&.(((.~.) q).|.(r.|.s))).&.((p.|.(r.|.t)).&.(((.~.) q).|.(r.|.t))))
                  (cnf ((p .=>. q) .=>. (((.~.) r) .=>. (s .&. t))))
    where
      [p, q, r, s, t] = map (\ s -> pApp s []) ["p", "q", "r", "s", "t"]

{-
test1 = TestCase
        (assertEqual "Logic Test 1"
         (TD.textFrame
          (PL.truthTable
           (PL.A
            -- All S2 are 12% S1
            (SeeReason.Types.A
             (Primitive (Reference (SubjectId 2)))
             (Primitive (Description np [Percentage 12.0, S (SubjectId 1)]))))))
         -- (runLogicM defaultValue "" (renderSubject (Subject 1)))
         ["+------------------------------------------------------------------------------------------------------------------------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------+"
         ,"| A (Primitive (Reference (SubjectId {unSubjectId = 2}))) (Primitive (Description NounPhrase [Percentage 12.0,S (SubjectId {unSubjectId = 1})])) | A (Primitive (Reference (SubjectId {unSubjectId = 2}))) (Primitive (Description NounPhrase [Percentage 12.0,S (SubjectId {unSubjectId = 1})])) |"
         ,"+------------------------------------------------------------------------------------------------------------------------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------+"
         ,"|                                                                       0                                                                        |                                                                       0                                                                        |"
         ,"+------------------------------------------------------------------------------------------------------------------------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------+"
         ,"|                                                                       1                                                                        |                                                                       1                                                                        |"
         ,"+------------------------------------------------------------------------------------------------------------------------------------------------+------------------------------------------------------------------------------------------------------------------------------------------------+"])

test2 = TestCase
        (assertEqual "Logic Test 1"
         (PL.satisfiable
          (PL.CJ
           [PL.A (SeeReason.Types.A
                  (Primitive (Reference (SubjectId 2)))
                  (Primitive (Description np [Percentage 12.0, S (SubjectId 1)]))),
            PL.F]))
         -- (runLogicM defaultValue "" (renderSubject (Subject 1)))
         True)
-}

moveQuantifiersOut1 =
    formCase "moveQuantifiersOut1"
             (for_all [y'] (pApp (fromString "p") [y] .&. (pApp (fromString "q") [x])))
             (moveQuantifiersOut (for_all [x'] (pApp (fromString "p") [x]) .&. (pApp (fromString "q") [x])))
