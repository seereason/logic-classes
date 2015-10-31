{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing -fno-warn-orphans #-}
module Logic (tests) where

import Common ({-instance Atom MyAtom MyTerm V-})
import Data.List as List (map)
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Instances.Test (MyFormula, MyAtom, MyTerm)
import Data.Logic.Satisfiable (theorem, inconsistant)
import Data.Map as Map (singleton)
import Data.Set.Extra as Set (Set, singleton, toList, empty, fromList, map {-, minView, fold-})
import Data.String (IsString(fromString))
import FOL (vt, (∀), pApp, fv, (.=.), exists, for_all, applyPredicate, fApp,
            HasApply(TermOf, PredOf), HasApplyAndEquate(equate), V(V), Predicate, subst, IsFirstOrder, IsQuantified(VarOf), IsTerm(FunOf, TVarOf))
import Formulas ((.~.), atomic, IsCombinable(..), IsFormula(AtomOf), (⇒))
import Lib (Marked)
import Lit (IsLiteral)
import Pretty (assertEqual', Pretty(pPrint))
import Prop (IsPropositional, list_conj, list_disj, Literal, markLiteral, markPropositional, Propositional,
             simpcnf, TruthTable(..), TruthTable, truthTable, unmarkLiteral)
import Skolem (HasSkolem(..), runSkolem, skolemize, pnf, simpcnf', Function)
import Test.HUnit
import qualified TextDisplay as TD

tests :: Test
tests = TestLabel "Test.Logic" $ TestList [precTests, normalTests, theoremTests]

{-
formCase :: (IsQuantified TFormula TAtom V, HasEquality TAtom Pr TTerm, Term TTerm V AtomicFunction) =>
            String -> TFormula -> TFormula -> Test
formCase s expected input = TestLabel s $ TestCase (assertEqual s expected input)
-}

-- instance IsAtom (Predicate Pr (PTerm V AtomicFunction))

precTests :: Test
precTests =
    TestList
    [ let label = "Logic - prec test 1" in
      TestLabel label (TestCase (assertEqual label
                                 ((a .&. b) .|. c)
                                 (a .&. b .|. c)))
      -- You can't apply .~. without parens:
      -- :type (.~. a)   -> (FormulaPF -> t) -> t
      -- :type ((.~.) a) -> FormulaPF
    , let label = "Logic - prec test 2" in
      TestLabel label (TestCase (assertEqual label
                                 (((.~.) a) .&. b)
                                 ((.~.) a .&. b :: MyFormula)))
    -- I switched the precedence of .&. and .|. from infixl to infixr to get
    -- some of the test cases to match the answers given on the miami.edu site,
    -- but maybe I should switch them back and adjust the answer given in the
    -- test case.
    , let label = "Logic - prec test 3" in
      TestLabel label (TestCase (assertEqual label
                                 ((a .&. b) .&. c) -- infixl, with infixr we get (a .&. (b .&. c))
                                 (a .&. b .&. c :: MyFormula)))
    , let -- x = vt "x" :: MyTerm
          y = vt "y" :: MyTerm
          -- This is not the desired result, but it is the result we
          -- will get due to the fact that function application
          -- precedence is always 10, and that rule applies when you
          -- put the operator in parentheses.  This means that direct
          -- input of examples from Harrison won't always work.
          expected = ((∀) "y" (pApp "g" [y])) ⇒ (pApp "f" [y]) :: MyFormula
          input =     (∀) "y" (pApp "g" [y])  ⇒ (pApp "f" [y]) :: MyFormula in
      let label = "Logic - prec test 4" in
      TestLabel label (TestCase (assertEqual label expected input))
    , TestCase (assertEqual "Logic - Find a free variable"
                (fv (for_all "x" (x .=. y) :: MyFormula))
                (Set.singleton "y"))
{-
    , let a = Combine (BinOp
                       (Combine (BinOp
                                 T
                                 (:=>:)
                                 (Combine (BinOp T (:&:) T))))
                       (:&:)
                       (Combine (BinOp
                                 (Combine (BinOp T (:&:) T))
                                 (:=>:)
                                 (Combine (BinOp T (:&:) T)))))
          b = Combine (BinOp
                       (Combine (BinOp
                                 T
                                 (:=>:)
                                 (Combine (BinOp
                                           (Combine (BinOp T (:&:) T))
                                           (:&:)
                                           (Combine (BinOp T (:&:) T))))))
                       (:=>:)
                       (Combine (BinOp T (:&:) T))) in
      ()
-}
    , TestCase (assertEqual "Logic - Substitute a variable"
                (List.map sub
                         [ for_all "x" (x .=. y) {- :: Formula String String -}
                         , for_all "y" (x .=. y) {- :: Formula String String -} ])
                [ for_all "x" (x .=. z) :: MyFormula
                , for_all "y" (z .=. y) :: MyFormula ])
    ]
    where
      sub f = subst (Map.singleton (head . Set.toList . fv $ f) (vt "z")) f
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

x :: MyTerm
x = vt (fromString "x")
y :: MyTerm
y = vt (fromString "y")
z :: MyTerm
z = vt (fromString "z")

normalTests :: Test
normalTests =
    let s = pApp "S"
        h = pApp "H"
        m = pApp "M"
        x' = vt "x'" :: MyTerm
        for_all' x fm = for_all (fromString x) fm
        exists' x fm = exists (fromString x) fm
    in
    TestList
    [TestCase (assertEqual
               "nnf"
               (show (pPrint (for_all' "x" (exists' "x'" ((s[x'] .&. ((.~.)(h[x'])) .|. h[x'] .&. ((.~.)(m[x']))) .|. ((.~.)(s[x])) .|. m[x])) :: MyFormula)))
               -- <<forall x. exists x'. (S(x') /\ ~H(x') \/ H(x') /\ ~M(x')) \/ ~S(x) \/ M(x)>>
               -- ∀x. ∃x'. ((S(x') ∧ ¬H(x') ∨ H(x') ∧ ¬M(x')) ∨ ¬S(x) ∨ M(x))
               (show
                (pPrint
                 (pnf (((for_all' "x" (s[x] .=>. h[x])) .&. (for_all "x" (h[x] .=>. m[x]))) .=>.
                    (for_all "x" (s[x] .=>. m[x])) :: MyFormula) :: MyFormula))))]

-- |Here is an example of automatic conversion from a IsQuantified
-- instance to a IsPropositional instance.  The result is PropForm
-- a where a is the original type, but the a values will always be
-- "atomic" formulas, never the operators which can be converted into
-- the corresponding operator of a IsPropositional instance.
{-
test9a :: Test
test9a = TestCase
           (assertEqual "Logic - convert to PropLogic"
            expected
            (flatten (cnf' (for_all "x" (for_all "y" (q [x, y] .<=>. for_all "z" (f [z, x] .<=>. f [z, y])))))))
    where
      f = pApp "f"
      q = pApp "q"
      expected :: PropForm MyFormula
      expected = CJ [DJ [N (A (pApp ("q") [vt (V "x"),vt (V "y")])),
                         N (A (pApp ("f") [vt (V "z"),vt (V "x")])),
                         A (pApp ("f") [vt (V "z"),vt (V "y")])],
                     DJ [N (A (pApp ("q") [vt (V "x"),vt (V "y")])),
                         N (A (pApp ("f") [vt (V "z"),vt (V "y")])),
                         A (pApp ("f") [vt (V "z"),vt (V "x")])],
                     DJ [A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "x")]),
                         A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "y")]),
                         A (pApp ("q") [vt (V "x"),vt (V "y")])],
                     DJ [N (A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "y")])),
                         A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "y")]),
                         A (pApp ("q") [vt (V "x"),vt (V "y")])],
                     DJ [A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "x")]),
                         N (A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "x")])),
                         A (pApp ("q") [vt (V "x"),vt (V "y")])],
                     DJ [N (A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "y")])),
                         N (A (pApp ("f") [fApp (Skolem 1) [vt (V "x"),vt (V "y"),vt (V "z")],vt (V "x")])),
                         A (pApp ("q") [vt (V "x"),vt (V "y")])]]

moveQuantifiersOut1 :: Test
moveQuantifiersOut1 =
    myTest "Logic - moveQuantifiersOut1"
             (for_all "x2" ((pApp ("p") [vt ("x2")]) .&. ((pApp ("q") [vt ("x")]))))
             (prenexNormalForm (for_all "x" (pApp (fromString "p") [x]) .&. (pApp (fromString "q") [x])))

skolemize1 :: Test
skolemize1 =
    myTest "Logic - skolemize1" expected formula
    where
      expected :: MyFormula
      expected = for_all [V "y",V "z"] (for_all [V "v"] (pApp "P" [fApp (toSkolem 1) [], y, z, fApp ((toSkolem 2)) [y, z], v, fApp (toSkolem 3) [y, z, v]]))
      formula :: MyFormula
      formula = (snf' (exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w])))))))

skolemize2 :: Test
skolemize2 =
    myTest "Logic - skolemize2" expected formula
    where
      expected :: MyFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [],y])
      formula :: MyFormula
      formula = snf' (exists ["x"] (for_all ["y"] (pApp "loves" [x, y])))

skolemize3 :: Test
skolemize3 =
    myTest "Logic - skolemize3" expected formula
    where
      expected :: MyFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [y],y])
      formula :: MyFormula
      formula = snf' (for_all ["y"] (exists ["x"] (pApp "loves" [x, y])))
-}
{-
inf1 :: Test
inf1 =
    myTest "Logic - inf1" expected formula
    where
      expected :: MyFormula
      expected = ((pApp ("p") [vt ("x")]) .=>. (((pApp ("q") [vt ("x")]) .|. ((pApp ("r") [vt ("x")])))))
      formula :: {- ImplicativeNormalFormula inf (C.Sentence V String AtomicFunction) (C.Term V AtomicFunction) V String AtomicFunction => -} MyFormula
      formula = convertFOF id id id (implicativeNormalForm (convertFOF id id id (for_all ["x"] (p [x] .=>. (q [x] .|. r [x]))) :: C.Sentence V String AtomicFunction) :: C.Sentence V String AtomicFunction)
-}

equality1 :: MyFormula
equality1 = for_all "x" ( x .=. x) .=>. for_all "x" (exists "y" ((x .=. y))) :: MyFormula
equality1expected :: (Bool, (Set (Set (Marked Literal (Marked Propositional MyFormula))), TruthTable MyAtom))
equality1expected = (False,(fromList [fromList [markLiteral (markPropositional (vt "x" .=. fApp (toSkolem "y")[vt "x"])),
                                                markLiteral (markPropositional ((.~.) (fApp (toSkolem "x")[] .=. fApp (toSkolem "x")[])))]],
                            TruthTable [equate (vt (V "x")) ((fApp (toSkolem (V "y") :: Function)[vt (V "x")] :: MyTerm)),
                                        equate (fApp (toSkolem (V "x"))[]) (fApp (toSkolem (V "x"))[] :: MyTerm)]
                                       [([False,False],True),
                                        ([False,True],False),
                                        ([True,False],True),
                                        ([True,True],True)]))
{-
equality1expected = (False, (fromList [fromList [markLiteral (markPropositional ((vt "x" :: MyTerm) .=. fApp (toSkolem "y")[vt (V "x")])),
                                                 markLiteral (markPropositional ((.~.) ((fApp (toSkolem "x")[] :: MyTerm) .=. (fApp (toSkolem "x")[] :: MyTerm))))]],
                             TruthTable ([{-(vt "x" :: MyTerm) .=. (fApp (toSkolem ("y" :: V)) [vt (V "x")] :: MyTerm),
                                          fApp (toSkolem "x") [] .=. fApp (toSkolem "x") []-}] :: [MyAtom])
                                        [([False,False],True),
                                         ([False,True],False),
                                         ([True,False],True),
                                         ([True,True],True)]))
-}
-- equality1expected = (False, (fromList [], TruthTable [] []))
{-
                     concat ["({{x = sKy[x], ¬(sKx[] = sKx[])}},\n",
                             " ([x = sKy[x], sKx[] = sKx[]],\n",
                             "  [([False, False], True), ([False, True], False),\n",
                             "   ([True, False], True), ([True, True], True)]))"]-}
equality2 :: MyFormula
equality2 = for_all "x" ( x .=. x .=>. for_all "x" ((.~.) (for_all "y" ((.~.) (x .=. y))))) -- convert existential
equality2expected :: (Bool, (Set (Set (Marked Literal (Marked Propositional MyFormula))), TruthTable MyAtom))
equality2expected = (False, (fromList [fromList [markLiteral (markPropositional (vt (V "x'") .=. fApp (toSkolem (V "y"))[vt (V "x'")])),
                                                 markLiteral (markPropositional ((.~.) (vt (V "x") .=. vt (V "x"))))]],
                             TruthTable [equate (vt (V "x")) (vt (V "x")),
                                         equate (vt (V "x'")) (fApp (toSkolem (V "y"))[vt "x'"] :: MyTerm)]
                                        [([False, False], True),
                                         ([False, True], True),
                                         ([True, False], False),
                                         ([True, True], True)]))
{-
equality2expected = (False,
                     concat ["({{x2 = sKy[x2], ¬x = x}},\n",
                             " ([x = x, x2 = sKy[x2]],\n",
                             "  [([False, False], True), ([False, True], True),\n",
                             "   ([True, False], False), ([True, True], True)]))"])
-}
theoremTests :: Test
theoremTests =
    let s = pApp "S" :: [MyTerm] -> MyFormula
        h = pApp "H" :: [MyTerm] -> MyFormula
        m = pApp "M" :: [MyTerm] -> MyFormula
        socrates1 = (for_all "x"   (s [x] .=>. h [x]) .&. for_all "x" (h [x] .=>. m [x]))  .=>.  for_all "x" (s [x] .=>. m [x])  :: MyFormula -- First two clauses grouped - compare to 5
        socrates2 =  for_all "x" (((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x]))  .=>.              (s [x] .=>. m [x])) :: MyFormula -- shared binding for x
        socrates3 = (for_all "x"  ((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x]))) .=>. (for_all "y" (s [y] .=>. m [y])) :: MyFormula -- First two clauses share x, third is renamed y
        socrates5 =  for_all "x"   (s [x] .=>. h [x]) .&. for_all "x" (h [x] .=>. m [x])   .=>.  for_all "x" (s [x] .=>. m [x])  :: MyFormula -- like 1, but less parens - check precedence
        socrates6 =  for_all "x"   (s [x] .=>. h [x]) .&. for_all "y" (h [y] .=>. m [y])   .=>.  for_all "z" (s [z] .=>. m [z])  :: MyFormula -- Like 5, but with variables renamed
        socrates7 =  for_all "x"  ((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x])   .&.               (m [x] .=>. ((.~.) (s [x])))) .&. (s [fApp "socrates" []])
    in
    TestList
    [ let label = "Logic - equality1" in
      TestLabel label (TestCase (assertEqual' label
                                 equality1expected
                                 (theorem equality1, table' equality1)))
    , let label = "Logic - equality2" in
      TestLabel label (TestCase (assertEqual' label
                                 equality2expected
                                 (theorem equality2, table' equality2)))
    , let label = "Logic - theorem test 1" in
      TestLabel label (TestCase (assertEqual label
                (True,(Set.empty, (TruthTable []{-Just (CJ [])-} [([],True)])))
                (theorem socrates2, table' socrates2)))
    , let label = "Logic - theorem test 1a" in
      TestLabel label (TestCase (assertEqual label
                (False,
                 False,
                 (fromList [fromList [atomic (applyPredicate "H" [fApp (toSkolem "x") []]),
                                      atomic (applyPredicate "M" [vt "y"]),
                                      atomic (applyPredicate "S" [fApp (toSkolem "x") []]),
                                      (.~.) (atomic (applyPredicate "S" [vt "y"]))],
                            fromList [atomic (applyPredicate "M" [vt "y"]),
                                      atomic (applyPredicate "S" [fApp (toSkolem "x") []]),
                                      (.~.) (atomic (applyPredicate "M" [fApp (toSkolem "x") []])),
                                      (.~.) (atomic (applyPredicate "S" [vt "y"]))],
                            fromList [atomic (applyPredicate "M" [vt "y"]),
                                      (.~.) (atomic (applyPredicate "H" [fApp (toSkolem "x") []])),
                                      (.~.) (atomic (applyPredicate "M" [fApp (toSkolem "x") []])),
                                      (.~.) (atomic (applyPredicate "S" [vt "y"]))]],
                 (TruthTable
                  [(applyPredicate "H" [fApp (toSkolem "x") []]),
                   (applyPredicate "M" [vt ("y")]),
                   (applyPredicate "M" [fApp (toSkolem "x") []]),
                   (applyPredicate "S" [vt ("y")]),
                   (applyPredicate "S" [fApp (toSkolem "x") []])]
                  [([False,     False,  False,  False,  False], True),
                   ([False,     False,  False,  False,  True],  True),
                   ([False,     False,  False,  True,   False], False),
                   ([False,     False,  False,  True,   True],  True),
                   ([False,     False,  True,   False,  False], True),
                   ([False,     False,  True,   False,  True],  True),
                   ([False,     False,  True,   True,   False], False),
                   ([False,     False,  True,   True,   True],  True),
                   ([False,     True,   False,  False,  False], True),
                   ([False,     True,   False,  False,  True],  True),
                   ([False,     True,   False,  True,   False], True),
                   ([False,     True,   False,  True,   True],  True),
                   ([False,     True,   True,   False,  False], True),
                   ([False,     True,   True,   False,  True],  True),
                   ([False,     True,   True,   True,   False], True),
                   ([False,     True,   True,   True,   True],  True),
                   ([True,      False,  False,  False,  False], True),
                   ([True,      False,  False,  False,  True],  True),
                   ([True,      False,  False,  True,   False], True),
                   ([True,      False,  False,  True,   True],  True),
                   ([True,      False,  True,   False,  False], True),
                   ([True,      False,  True,   False,  True],  True),
                   ([True,      False,  True,   True,   False], False),
                   ([True,      False,  True,   True,   True],  False),
                   ([True,      True,   False,  False,  False], True),
                   ([True,      True,   False,  False,  True],  True),
                   ([True,      True,   False,  True,   False], True),
                   ([True,      True,   False,  True,   True],  True),
                   ([True,      True,   True,   False,  False], True),
                   ([True,      True,   True,   False,  True],  True),
                   ([True,      True,   True,   True,   False], True),
                   ([True,      True,   True,   True,   True],  True)])))

                (theorem socrates3, inconsistant socrates3,
                 table' socrates3)))
    , let label = "socrates1 truth table" in
      TestLabel label (TestCase (assertEqual label
             (let skx = fApp (toSkolem "x") in
              (fromList [fromList [atomic (applyPredicate "H" [fApp (toSkolem "x") []]),
                                   atomic (applyPredicate "M" [vt "x"]),
                                   atomic (applyPredicate "S" [fApp (toSkolem "x") []]),
                                   (.~.) (atomic (applyPredicate "S" [vt "x"]))],
                         fromList [atomic (applyPredicate "M" [vt "x"]),
                                   atomic (applyPredicate "S" [fApp (toSkolem "x") []]),
                                   (.~.) (atomic (applyPredicate "M" [fApp (toSkolem "x") []])),
                                   (.~.) (atomic (applyPredicate "S" [vt "x"]))],
                         fromList [atomic (applyPredicate "M" [vt "x"]),
                                   (.~.) (atomic (applyPredicate "H" [fApp (toSkolem "x") []])),
                                   (.~.) (atomic (applyPredicate "M" [fApp (toSkolem "x") []])),
                                   (.~.) (atomic (applyPredicate "S" [vt "x"]))]],
              (TruthTable
               [(applyPredicate "H" [skx []]),
                (applyPredicate "M" [x]),
                (applyPredicate "M" [skx []]),
                (applyPredicate "S" [x]),
                (applyPredicate "S" [skx []])]
               -- Clauses are always true if x is not socrates
               -- Nothing,
               {- (Just (CJ [DJ [A (h[skx[]]), A (m[x]),     A (s[skx[]]), N (s[x])],  -- false when x is socrates and not mortal, and skx is socrates and human
                          DJ [A (m[x]),     A (s[skx[]]), N (A (m[skx[]])), N (s[x])],
                          DJ [A (m[x]),     N (A (h[x])), N (A (m[skx[]])), N (s[x])]])) -}
            --    h[skx] m[x] m[skx] s[x] s[skx]
               [([False,False,False,False,False],True),
                ([False,False,False,False,True], True),
                ([False,False,False,True, False],False),
                ([False,False,False,True, True], True),
                ([False,False,True, False,False],True),
                ([False,False,True, False,True], True),
                ([False,False,True, True, False],False),
                ([False,False,True, True, True], True),
                ([False,True, False,False,False],True),
                ([False,True, False,False,True], True),
                ([False,True, False,True, False],True),
                ([False,True, False,True, True], True),
                ([False,True, True, False,False],True),
                ([False,True, True, False,True], True),
                ([False,True, True, True, False],True),
                ([False,True, True, True, True], True),
                ([True, False,False,False,False],True),
                ([True, False,False,False,True], True),
                ([True, False,False,True, False],True),
                ([True, False,False,True, True], True),
                ([True, False,True, False,False],True),
                ([True, False,True, False,True], True),
                ([True, False,True, True, False],False),
                ([True, False,True, True, True], False),
                ([True, True, False,False,False],True),
                ([True, True, False,False,True], True),
                ([True, True, False,True, False],True),
                ([True, True, False,True, True], True),
                ([True, True, True, False,False],True),
                ([True, True, True, False,True], True),
                ([True, True, True, True, False],True),
                ([True, True, True, True, True], True)])))
                (table' socrates1)))

    , let skx = fApp (toSkolem "x")
          {- sky = fApp (toSkolem "y") -} in
      let label = "Socrates formula skolemized" in
      TestLabel label (TestCase (assertEqual label
                 (((pApp "S" [skx []] .&. (.~.)(pApp "H" [skx []]) .|. pApp "H" [skx[]] .&. (.~.)(pApp "M" [skx []])) .|.
                   ((.~.)(pApp "S" [x]) .|. pApp "M" [x])))
                 (runSkolem (skolemize id socrates5) :: Marked Propositional MyFormula)))

    , let skx = fApp (toSkolem "x")
          sky = fApp (toSkolem "y") in
      let label = "Socrates formula skolemized" in
      TestLabel label (TestCase (assertEqual label
                 ((pApp "S" [skx []] .&. (.~.)(pApp "H" [skx []]) .|. pApp "H" [sky[]] .&. (.~.)(pApp "M" [sky []])) .|.
                  ((.~.)(pApp "S" [z]) .|. pApp "M" [z]))
                 (runSkolem (skolemize id socrates6) :: Marked Propositional MyFormula)))

    , let label = "Logic - socrates is not mortal" in
      TestLabel label (TestCase (assertEqual' label
                (False,
                 False,
                 (fromList [fromList [atomic (applyPredicate "H" [vt "x"]),
                                      (.~.) (atomic (applyPredicate "S" [vt "x"]))],
                            fromList [atomic (applyPredicate "M" [vt "x"]),
                                      (.~.) (atomic (applyPredicate "H" [vt "x"]))],
                            fromList [atomic (applyPredicate "S" [fApp "socrates" []])],
                            fromList [(.~.) (atomic (applyPredicate "M" [vt "x"])),
                                      (.~.) (atomic (applyPredicate "S" [vt "x"]))]],
                 (TruthTable
                  [(applyPredicate ("H") [vt ("x")]),
                   (applyPredicate ("M") [vt ("x")]),
                   (applyPredicate ("S") [vt ("x")]),
                   (applyPredicate ("S") [fApp ("socrates") []])]
                  [([False,False,False,False],False),
                   ([False,False,False,True],True),
                   ([False,False,True,False],False),
                   ([False,False,True,True],False),
                   ([False,True,False,False],False),
                   ([False,True,False,True],True),
                   ([False,True,True,False],False),
                   ([False,True,True,True],False),
                   ([True,False,False,False],False),
                   ([True,False,False,True],False),
                   ([True,False,True,False],False),
                   ([True,False,True,True],False),
                   ([True,True,False,False],False),
                   ([True,True,False,True],True),
                   ([True,True,True,False],False),
                   ([True,True,True,True],False)])),
                 toSS [[(pApp ("S") [fApp ("socrates") []])],
                       [(pApp ("H") [vt ("x")]),((.~.) (pApp ("S") [vt ("x")]))],
                       [(pApp ("M") [vt ("x")]),((.~.) (pApp ("H") [vt ("x")]))],
                       [((.~.) (pApp ("M") [vt ("x")])),((.~.) (pApp ("S") [vt ("x")]))]])
                -- This represents a list of beliefs like those in our
                -- database: socrates is a man, all men are mortal,
                -- each with its own quantified variable.  In
                -- addition, we have an inconsistant belief, socrates
                -- is not mortal.  If we had a single variable this
                -- would be inconsistant, but as it stands it is an
                -- invalid argument, there are both 0 and 1 lines in
                -- the truth table.  If we go through the table and
                -- eliminate the lines where S(SkZ(x,y)) is true but M(SkZ(x,y)) is
                -- false (for any x) and those where H(x) is true but
                -- M(x) is false, the remaining lines would all be zero,
                -- the argument would be inconsistant (an anti-theorem.)
                -- How can we modify the formula to make these lines 0?
                (theorem socrates7, inconsistant socrates7, table' socrates7, simpcnf' socrates7 :: Set (Set MyFormula))))
    , let (formula :: MyFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "x" (pApp "L" [vt "x"])) .=>.                            -- Someone is a logician
              (.~.) (exists "x" (pApp "F" [vt "x"]))                           -- Someone / Nobody is funny
          input = table' formula
          expected = (fromList [fromList [atomic (applyPredicate "L" [fApp (toSkolem "x") []]),
                                          (.~.) (atomic (applyPredicate "F" [vt "x'"])),
                                          (.~.) (atomic (applyPredicate "L" [vt "x"]))],
                                fromList [(.~.) (atomic (applyPredicate "F" [vt "x'"])),
                                          (.~.) (atomic (applyPredicate "F" [fApp (toSkolem "x") []])),
                                          (.~.) (atomic (applyPredicate "L" [vt "x"]))]],
                      (TruthTable
                       [(applyPredicate ("F") [vt ("x'")]),
                       (applyPredicate ("F") [fApp (toSkolem "x") []]),
                       (applyPredicate ("L") [vt ("x")]),
                       (applyPredicate ("L") [fApp (toSkolem "x") []])]
                      [([False,False,False,False],True),
                       ([False,False,False,True],True),
                       ([False,False,True,False],True),
                       ([False,False,True,True],True),
                       ([False,True,False,False],True),
                       ([False,True,False,True],True),
                       ([False,True,True,False],True),
                       ([False,True,True,True],True),
                       ([True,False,False,False],True),
                       ([True,False,False,True],True),
                       ([True,False,True,False],False),
                       ([True,False,True,True],True),
                       ([True,True,False,False],True),
                       ([True,True,False,True],True),
                       ([True,True,True,False],False),
                       ([True,True,True,True],False)]))
      in let label = "Logic - gensler189" in
         TestLabel label (TestCase (assertEqual' label expected input))
    , let (formula :: MyFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "y" (pApp "L" [vt (fromString "y")])) .=>.           -- Someone is a logician
              (.~.) (exists "z" (pApp "F" [vt "z"]))                       -- Someone / Nobody is funny
          input = table' formula
          expected = (fromList [fromList [atomic (applyPredicate (p "L") [fApp (toSkolem "x") []]),
                                          (.~.) (atomic (applyPredicate (p "F") [vt "z"])),
                                          (.~.) (atomic (applyPredicate (p "L") [vt "y"]))],
                                fromList [(.~.) (atomic (applyPredicate (p "F") [vt "z"])),
                                          (.~.) (atomic (applyPredicate (p "F") [fApp (toSkolem "x") []])),
                                          (.~.) (atomic (applyPredicate (p "L") [vt "y"]))]],
                      (TruthTable
                       [applyPredicate (p "F") [vt (V "z")],
                        applyPredicate (p "F") [fApp (toSkolem (V "x")) []],
                        applyPredicate (p "L") [vt (V "y")],
                        applyPredicate (p "L") [fApp (toSkolem (V "x")) []]]
                      [([False,False,False,False],True),
                       ([False,False,False,True],True),
                       ([False,False,True,False],True),
                       ([False,False,True,True],True),
                       ([False,True,False,False],True),
                       ([False,True,False,True],True),
                       ([False,True,True,False],True),
                       ([False,True,True,True],True),
                       ([True,False,False,False],True),
                       ([True,False,False,True],True),
                       ([True,False,True,False],False),
                       ([True,False,True,True],True),
                       ([True,True,False,False],True),
                       ([True,True,False,True],True),
                       ([True,True,True,False],False),
                       ([True,True,True,True],False)]))
      in let label = "Logic - gensler189 renamed" in
         TestLabel label (TestCase (assertEqual label expected input))
    ]

p :: String -> Predicate
p = fromString

toSS :: Ord a => [[a]] -> Set (Set a)
toSS = Set.fromList . List.map Set.fromList

{-
theorem5 =
    myTest "Logic - theorm test 2"
              (Just True)
              (theorem ((.~.) ((for_all "x" (((s [x] .=>. h [x]) .&.
                                               (h [x] .=>. m [x]))) .&.
                                exists "x" (s [x] .&.
                                             ((.~.) (m [x])))))))
-}

instance TD.Display MyFormula where
    textFrame x = [show x]
{-
    textFrame x = [quickShow x]
        where
          quickShow =
              foldF (\ _ -> error "Expecting atoms")
                    (\ _ _ _ -> error "Expecting atoms")
                    (\ _ _ _ -> error "Expecting atoms")
                    (\ t1 op t2 -> quickShowTerm t1 ++ quickShowOp op ++ quickShowTerm t2)
                    (\ p ts -> quickShowPred p ++ "(" ++ intercalate "," (map quickShowTerm ts) ++ ")")
          quickShowTerm =
              foldT quickShowVar
                    (\ f ts -> quickShowFn f ++ "(" ++ intercalate "," (map quickShowTerm ts) ++ ")")
          quickShowVar v = show v
          quickShowPred s = s
          quickShowFn (AtomicFunction s) = s
          quickShowOp (:=:) = "="
          quickShowOp (:!=:) = "!="
-}

{-
-- Truth table tests, find a more reasonable result value than [String].

(theorem1a, theorem1b, theorem1c, theorem1d) =
    ( myTest "Logic - truth table 1"
                (Just ["foo"])
                (prepare (for_all "x" (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))) >>=
                 return . TD.textFrame . truthTable) )
    where s = pApp "S"
          h = pApp "H"
          m = pApp "M"

type FormulaPF = Formula String String
type F = PropForm FormulaPF

prepare :: FormulaPF -> F
prepare formula = ({- flatten . -} fromJust . toPropositional convertA . cnf . (.~.) $ formula)

convertA = Just . A
-}
         {- forall formula atom term v p f.
         (IsQuantified formula atom v,
          IsPropositional formula atom,
          Atom atom term v,
          HasEquality atom p term,
          HasBoolean p, Eq p, Term term v f, IsLiteral formula atom v,
          Ord formula, Skolem f v, IsString v, Variable v, TD.Display formula) => -}

table :: forall formula atom p term v f.
         (atom ~ AtomOf formula, v ~ VarOf formula, v ~ TVarOf term, term ~ TermOf atom, p ~ PredOf atom, f ~ FunOf term,
          IsFirstOrder formula,
          IsPropositional formula,
          IsLiteral formula,
          HasSkolem f v,
          Atom atom term v,
          IsTerm term,
          Ord formula, Pretty formula, Ord atom) =>
         formula -> (Set (Set (Marked Literal (Marked Propositional formula))), TruthTable (AtomOf formula))
table f =
    -- truthTable :: Ord a => PropForm a -> TruthTable a
    (cnf, truthTable cnf')
    where
      cnf' :: Marked Propositional formula
      cnf' = unmarkLiteral $ list_conj (Set.map list_disj cnf :: Set (Marked Literal (Marked Propositional formula)))
      cnf :: Set (Set (Marked Literal (Marked Propositional formula)))
      cnf = simpcnf id (runSkolem (skolemize id f) :: Marked Propositional formula)
      -- fromSS = List.map Set.toList . Set.toList
      -- n f = (if negated f then (.~.) . atomic . (.~.) else atomic) $ f
      -- list_disj = setFoldr1 (.|.)
      -- list_conj = setFoldr1 (.&.)

table' :: MyFormula -> (Set (Set (Marked Literal (Marked Propositional MyFormula))), TruthTable MyAtom)
table' = table

{-
setFoldr1 :: (a -> a -> a) -> Set a -> a
setFoldr1 f s =
    case Set.minView s of
      Nothing -> error "setFoldr1"
      Just (x, s') -> Set.fold f x s'
-}
