{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing -fno-warn-orphans #-}
module Data.Logic.Tests.Logic (tests) where

import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..), (⇒))
import Data.Logic.Classes.Constants (Constants(..), true)
import Data.Logic.Classes.Equals (AtomEq, (.=.), pApp, pApp1, showAtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), showFirstOrder, (∀))
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Negate (negated, (.~.))
import Data.Logic.Classes.Pretty (pretty)
import Data.Logic.Classes.Propositional (PropositionalFormula)
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Harrison.FOL (fv, subst, list_conj, list_disj)
import Data.Logic.Harrison.Normal (trivial)
import Data.Logic.Harrison.Prop (TruthTable, truthTable)
import Data.Logic.Harrison.Skolem (runSkolem, skolemize, pnf)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (runNormal)
import Data.Logic.Satisfiable (theorem, inconsistant)
import Data.Logic.Tests.Common (TFormula, TAtom, TTerm, myTest)
import Data.Logic.Types.FirstOrder
import qualified Data.Map as Map
import qualified Data.Set.Extra as Set
import Data.Set.Extra (fromList)
import Data.String (IsString(fromString))
-- import PropLogic (PropForm(..), TruthTable, truthTable)
import qualified TextDisplay as TD
import Test.HUnit

tests :: Test
tests = TestLabel "Test.Logic" $ TestList [precTests, normalTests, theoremTests]

{-
formCase :: (FirstOrderFormula TFormula TAtom V, AtomEq TAtom Pr TTerm, Term TTerm V AtomicFunction) =>
            String -> TFormula -> TFormula -> Test
formCase s expected input = TestLabel s $ TestCase (assertEqual s expected input)
-}

precTests :: Test
precTests =
    TestList
    [ myTest "Logic - prec test 1"
               ((a .&. b) .|. c)
               (a .&. b .|. c)
      -- You can't apply .~. without parens:
      -- :type (.~. a)   -> (FormulaPF -> t) -> t
      -- :type ((.~.) a) -> FormulaPF
    , myTest "Logic - prec test 2"
               (((.~.) a) .&. b)
               ((.~.) a .&. b :: TFormula)
    -- I switched the precedence of .&. and .|. from infixl to infixr to get
    -- some of the test cases to match the answers given on the miami.edu site,
    -- but maybe I should switch them back and adjust the answer given in the
    -- test case.
    , myTest "Logic - prec test 3"
               ((a .&. b) .&. c) -- infixl, with infixr we get (a .&. (b .&. c))
               (a .&. b .&. c :: TFormula)
    , let x = vt "x" :: TTerm
          y = vt "y" :: TTerm
          -- This is not the desired result, but it is the result we
          -- will get due to the fact that function application
          -- precedence is always 10, and that rule applies when you
          -- put the operator in parentheses.  This means that direct
          -- input of examples from Harrison won't always work.
          expected = ((∀) "y" (pApp "g" [y])) ⇒ (pApp "f" [y]) :: TFormula
          input =     (∀) "y" (pApp "g" [y])  ⇒ (pApp "f" [y]) :: TFormula in
      myTest "Logic - prec test 4" expected input
    , TestCase (assertEqual "Logic - Find a free variable"
                (fv (for_all "x" (x .=. y) :: TFormula))
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
                (map sub
                         [ for_all "x" (x .=. y) {- :: Formula String String -}
                         , for_all "y" (x .=. y) {- :: Formula String String -} ])
                [ for_all "x" (x .=. z) :: TFormula
                , for_all "y" (z .=. y) :: TFormula ])
    ]
    where
      sub f = subst (Map.singleton (head . Set.toList . fv $ f) (vt "z")) f
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

x :: TTerm
x = vt (fromString "x")
y :: TTerm
y = vt (fromString "y")
z :: TTerm
z = vt (fromString "z")

normalTests =
    let s = pApp "S"
        h = pApp "H"
        m = pApp "M"
        x2 = vt "x2" :: TTerm
        for_all' x fm = for_all (fromString x) fm
        exists' x fm = exists (fromString x) fm
    in
    TestList
    [TestCase (assertEqual
               "nnf"
               (show (pretty (for_all' "x" (exists' "x2" ((s[x2] .&. ((.~.)(h[x2])) .|. h[x2] .&. ((.~.)(m[x2]))) .|. ((.~.)(s[x])) .|. m[x])) :: TFormula)))
               -- <<forall x. exists x'. (S(x') /\ ~H(x') \/ H(x') /\ ~M(x')) \/ ~S(x) \/ M(x)>>
               -- ∀x. ∃x2. ((S(x2) ∧ ¬H(x2) ∨ H(x2) ∧ ¬M(x2)) ∨ ¬S(x) ∨ M(x))
               (show
                (pretty
                 (pnf (((for_all' "x" (s[x] .=>. h[x])) .&. (for_all "x" (h[x] .=>. m[x]))) .=>.
                    (for_all "x" (s[x] .=>. m[x])) :: TFormula) :: TFormula))))]

-- |Here is an example of automatic conversion from a FirstOrderFormula
-- instance to a PropositionalFormula instance.  The result is PropForm
-- a where a is the original type, but the a values will always be
-- "atomic" formulas, never the operators which can be converted into
-- the corresponding operator of a PropositionalFormula instance.
{-
test9a :: Test
test9a = TestCase 
           (assertEqual "Logic - convert to PropLogic"
            expected
            (flatten (cnf' (for_all "x" (for_all "y" (q [x, y] .<=>. for_all "z" (f [z, x] .<=>. f [z, y])))))))
    where
      f = pApp "f"
      q = pApp "q"
      expected :: PropForm TFormula
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
      expected :: TFormula
      expected = for_all [V "y",V "z"] (for_all [V "v"] (pApp "P" [fApp (toSkolem 1) [], y, z, fApp ((toSkolem 2)) [y, z], v, fApp (toSkolem 3) [y, z, v]]))
      formula :: TFormula
      formula = (snf' (exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w])))))))

skolemize2 :: Test
skolemize2 =
    myTest "Logic - skolemize2" expected formula
    where
      expected :: TFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [],y])
      formula :: TFormula
      formula = snf' (exists ["x"] (for_all ["y"] (pApp "loves" [x, y])))

skolemize3 :: Test
skolemize3 =
    myTest "Logic - skolemize3" expected formula
    where
      expected :: TFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [y],y])
      formula :: TFormula
      formula = snf' (for_all ["y"] (exists ["x"] (pApp "loves" [x, y])))
-}
{-
inf1 :: Test
inf1 =
    myTest "Logic - inf1" expected formula
    where
      expected :: TFormula
      expected = ((pApp ("p") [vt ("x")]) .=>. (((pApp ("q") [vt ("x")]) .|. ((pApp ("r") [vt ("x")])))))
      formula :: {- ImplicativeNormalFormula inf (C.Sentence V String AtomicFunction) (C.Term V AtomicFunction) V String AtomicFunction => -} TFormula
      formula = convertFOF id id id (implicativeNormalForm (convertFOF id id id (for_all ["x"] (p [x] .=>. (q [x] .|. r [x]))) :: C.Sentence V String AtomicFunction) :: C.Sentence V String AtomicFunction)
-}

theoremTests :: Test
theoremTests =
    let s = pApp "S"
        h = pApp "H"
        m = pApp "M"
        socrates1 = (for_all "x"   (s [x] .=>. h [x]) .&. for_all "x" (h [x] .=>. m [x]))  .=>.  for_all "x" (s [x] .=>. m [x])  :: TFormula -- First two clauses grouped - compare to 5
        socrates2 =  for_all "x" (((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x]))  .=>.              (s [x] .=>. m [x])) :: TFormula -- shared binding for x
        socrates3 = (for_all "x"  ((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x]))) .=>. (for_all "y" (s [y] .=>. m [y])) :: TFormula -- First two clauses share x, third is renamed y
        socrates5 =  for_all "x"   (s [x] .=>. h [x]) .&. for_all "x" (h [x] .=>. m [x])   .=>.  for_all "x" (s [x] .=>. m [x])  :: TFormula -- like 1, but less parens - check precedence 
        socrates6 =  for_all "x"   (s [x] .=>. h [x]) .&. for_all "y" (h [y] .=>. m [y])   .=>.  for_all "z" (s [z] .=>. m [z])  :: TFormula -- Like 5, but with variables renamed
        socrates7 =  for_all "x"  ((s [x] .=>. h [x]) .&.             (h [x] .=>. m [x])   .&.               (m [x] .=>. ((.~.) (s [x])))) .&. (s [fApp "socrates" []]) in 
    TestList
    [ myTest "Logic - theorem test 1"
                (True,(Set.empty, ([]{-Just (CJ [])-},[([],True)])))
                (runNormal (theorem socrates2), table socrates2)
    , myTest "Logic - theorem test 1a"
                (False,
                 False,
                 (fromList [fromList [Predicate (Apply "H" [FunApp (toSkolem "x") []]),
                                      Predicate (Apply "M" [Var "y"]),
                                      Predicate (Apply "S" [FunApp (toSkolem "x") []]),
                                      Combine ((:~:) (Predicate (Apply "S" [Var "y"])))],
                            fromList [Predicate (Apply "M" [Var "y"]),
                                      Predicate (Apply "S" [FunApp (toSkolem "x") []]),
                                      Combine ((:~:) (Predicate (Apply "M" [FunApp (toSkolem "x") []]))),
                                      Combine ((:~:) (Predicate (Apply "S" [Var "y"])))],
                            fromList [Predicate (Apply "M" [Var "y"]),
                                      Combine ((:~:) (Predicate (Apply "H" [FunApp (toSkolem "x") []]))),
                                      Combine ((:~:) (Predicate (Apply "M" [FunApp (toSkolem "x") []]))),
                                      Combine ((:~:) (Predicate (Apply "S" [Var "y"])))]],
                 ([(Apply "H" [fApp (toSkolem "x") []]),
                   (Apply "M" [vt ("y")]),
                   (Apply "M" [fApp (toSkolem "x") []]),
                   (Apply "S" [vt ("y")]),
                   (Apply "S" [fApp (toSkolem "x") []])],
                  [([False,	False,	False,	False,	False],	True),
                   ([False,	False,	False,	False,	True],	True),
                   ([False,	False,	False,	True,	False],	False),
                   ([False,	False,	False,	True,	True],	True),
                   ([False,	False,	True,	False,	False],	True),
                   ([False,	False,	True,	False,	True],	True),
                   ([False,	False,	True,	True,	False],	False),
                   ([False,	False,	True,	True,	True],	True),
                   ([False,	True,	False,	False,	False],	True),
                   ([False,	True,	False,	False,	True],	True),
                   ([False,	True,	False,	True,	False],	True),
                   ([False,	True,	False,	True,	True],	True),
                   ([False,	True,	True,	False,	False],	True),
                   ([False,	True,	True,	False,	True],	True),
                   ([False,	True,	True,	True,	False],	True),
                   ([False,	True,	True,	True,	True],	True),
                   ([True,	False,	False,	False,	False],	True),
                   ([True,	False,	False,	False,	True],	True),
                   ([True,	False,	False,	True,	False],	True),
                   ([True,	False,	False,	True,	True],	True),
                   ([True,	False,	True,	False,	False],	True),
                   ([True,	False,	True,	False,	True],	True),
                   ([True,	False,	True,	True,	False],	False),
                   ([True,	False,	True,	True,	True],	False),
                   ([True,	True,	False,	False,	False],	True),
                   ([True,	True,	False,	False,	True],	True),
                   ([True,	True,	False,	True,	False],	True),
                   ([True,	True,	False,	True,	True],	True),
                   ([True,	True,	True,	False,	False],	True),
                   ([True,	True,	True,	False,	True],	True),
                   ([True,	True,	True,	True,	False],	True),
                   ([True,	True,	True,	True,	True],	True)])))
                
                (runNormal (theorem socrates3),
                 runNormal (inconsistant socrates3),
                 table socrates3)
    , myTest "socrates1 truth table"
             (let skx = fApp (toSkolem "x") in
              (fromList [fromList [Predicate (Apply "H" [FunApp (toSkolem "x") []]),
                                   Predicate (Apply "M" [Var "x"]),
                                   Predicate (Apply "S" [FunApp (toSkolem "x") []]),
                                   Combine ((:~:) (Predicate (Apply "S" [Var "x"])))],
                         fromList [Predicate (Apply "M" [Var "x"]),
                                   Predicate (Apply "S" [FunApp (toSkolem "x") []]),
                                   Combine ((:~:) (Predicate (Apply "M" [FunApp (toSkolem "x") []]))),
                                   Combine ((:~:) (Predicate (Apply "S" [Var "x"])))],
                         fromList [Predicate (Apply "M" [Var "x"]),
                                   Combine ((:~:) (Predicate (Apply "H" [FunApp (toSkolem "x") []]))),
                                   Combine ((:~:) (Predicate (Apply "M" [FunApp (toSkolem "x") []]))),
                                   Combine ((:~:) (Predicate (Apply "S" [Var "x"])))]],
              ([(Apply "H" [skx []]),
                (Apply "M" [x]),
                (Apply "M" [skx []]),
                (Apply "S" [x]),
                (Apply "S" [skx []])],
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
                (table socrates1)

    , let skx = fApp (toSkolem "x")
          {- sky = fApp (toSkolem "y") -} in
      myTest "Socrates formula skolemized"
              -- ((s[skx []] .&. (.~.)(h[skx []]) .|. h[sky[]] .&. (.~.)(m[sky []])) .|. (.~.)(s[z]) .|. m[z])
                 ((s[skx []] .&. (.~.)(h[skx []]) .|. h[skx[]] .&. (.~.)(m[skx []])) .|. (.~.)(s[x]) .|. m[x])
                 (runSkolem (skolemize id socrates5) :: TFormula)

    , let skx = fApp (toSkolem "x")
          sky = fApp (toSkolem "y") in
      myTest "Socrates formula skolemized"
              -- ((s[skx []] .&. (.~.)(h[skx []]) .|. h[sky[]] .&. (.~.)(m[sky []])) .|. (.~.)(s[z]) .|. m[z])
                 ((s[skx []] .&. (.~.)(h[skx []]) .|. h[sky[]] .&. (.~.)(m[sky []])) .|. (.~.)(s[z]) .|. m[z])
                 (runSkolem (skolemize id socrates6) :: TFormula)

    , myTest "Logic - socrates is not mortal"
                (False,
                 False,
                 (fromList [fromList [Predicate (Apply "H" [Var "x"]),
                                      Combine ((:~:) (Predicate (Apply "S" [Var "x"])))],
                            fromList [Predicate (Apply "M" [Var "x"]),
                                      Combine ((:~:) (Predicate (Apply "H" [Var "x"])))],
                            fromList [Predicate (Apply "S" [FunApp "socrates" []])],
                            fromList [Combine ((:~:) (Predicate (Apply "M" [Var "x"]))),
                                      Combine ((:~:) (Predicate (Apply "S" [Var "x"])))]],
                 ([(Apply ("H") [vt ("x")]),
                   (Apply ("M") [vt ("x")]),
                   (Apply ("S") [vt ("x")]),
                   (Apply ("S") [fApp ("socrates") []])],
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
                 toSS [[(pApp ("H") [vt ("x")]),((.~.) (pApp ("S") [vt ("x")]))],
                       [(pApp ("M") [vt ("x")]),((.~.) (pApp ("H") [vt ("x")]))],
                       [(pApp ("S") [fApp ("socrates") []])],
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
                (runNormal (theorem socrates7), runNormal (inconsistant socrates7), table socrates7, runNormal (clauseNormalForm socrates7) :: Set.Set (Set.Set TFormula))
    , let (formula :: TFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "x" (pApp "L" [vt "x"])) .=>.                            -- Someone is a logician
              (.~.) (exists "x" (pApp "F" [vt "x"]))                           -- Someone / Nobody is funny
          input = table formula
          expected = (fromList [fromList [Predicate (Apply "L" [FunApp (toSkolem "x") []]),
                                          Combine ((:~:) (Predicate (Apply "F" [Var "x2"]))),
                                          Combine ((:~:) (Predicate (Apply "L" [Var "x"])))],
                                fromList [Combine ((:~:) (Predicate (Apply "F" [Var "x2"]))),
                                          Combine ((:~:) (Predicate (Apply "F" [FunApp (toSkolem "x") []]))),
                                          Combine ((:~:) (Predicate (Apply "L" [Var "x"])))]],
                      ([(Apply ("F") [vt ("x2")]),
                       (Apply ("F") [fApp (toSkolem "x") []]),
                       (Apply ("L") [vt ("x")]),
                       (Apply ("L") [fApp (toSkolem "x") []])],
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
      in myTest "Logic - gensler189" expected input
    , let (formula :: TFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "y" (pApp "L" [vt (fromString "y")])) .=>.           -- Someone is a logician
              (.~.) (exists "z" (pApp "F" [vt "z"]))                       -- Someone / Nobody is funny
          input = table formula
          expected = (fromList [fromList [Predicate (Apply "L" [FunApp (toSkolem "x") []]),
                                          Combine ((:~:) (Predicate (Apply "F" [Var "z"]))),
                                          Combine ((:~:) (Predicate (Apply "L" [Var "y"])))],
                                fromList [Combine ((:~:) (Predicate (Apply "F" [Var "z"]))),
                                          Combine ((:~:) (Predicate (Apply "F" [FunApp (toSkolem "x") []]))),
                                          Combine ((:~:) (Predicate (Apply "L" [Var "y"])))]],
                      ([(Apply ("F") [vt ("z")]),
                       (Apply ("F") [fApp (toSkolem "x") []]),
                       (Apply ("L") [vt ("y")]),
                       (Apply ("L") [fApp (toSkolem "x") []])],
                      [([False,False,False,False],True),([False,False,False,True],True),([False,False,True,False],True),([False,False,True,True],True),([False,True,False,False],True),([False,True,False,True],True),([False,True,True,False],True),([False,True,True,True],True),([True,False,False,False],True),([True,False,False,True],True),([True,False,True,False],False),([True,False,True,True],True),([True,True,False,False],True),([True,True,False,True],True),([True,True,True,False],False),([True,True,True,True],False)]))
      in myTest "Logic - gensler189 renamed" expected input
    ]

toSS :: Ord a => [[a]] -> Set.Set (Set.Set a)
toSS = Set.fromList . map Set.fromList

{-
theorem5 =
    myTest "Logic - theorm test 2"
              (Just True)
              (theorem ((.~.) ((for_all "x" (((s [x] .=>. h [x]) .&.
                                               (h [x] .=>. m [x]))) .&.
                                exists "x" (s [x] .&.
                                             ((.~.) (m [x])))))))
-}

instance TD.Display TFormula where
    textFrame x = [showFirstOrder showAtomEq x]
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
         (FirstOrderFormula formula atom v,
          PropositionalFormula formula atom,
          Atom atom term v,
          AtomEq atom p term,
          Constants p, Eq p, Term term v f, Literal formula atom v,
          Ord formula, Skolem f v, IsString v, Variable v, TD.Display formula) => -}

table :: forall formula atom term v f.
         (FirstOrderFormula formula atom v,
          PropositionalFormula formula atom,
          Literal formula atom v,
          Atom atom term v,
          Term term v f,
          Ord formula, Ord atom) =>
         formula -> (Set.Set (Set.Set formula), TruthTable atom)
table f =
    -- truthTable :: Ord a => PropForm a -> TruthTable a
    (cnf, truthTable cnf')
    where
      cnf' :: formula
      cnf' = list_conj (Set.map list_disj cnf :: Set.Set formula) -- CJ (map (DJ . map n) cnf)
      cnf :: Set.Set (Set.Set formula)
      cnf = runNormal (clauseNormalForm f)
      fromSS = map Set.toList . Set.toList
      -- n f = (if negated f then (.~.) . atomic . (.~.) else atomic) $ f
      -- list_disj = setFoldr1 (.|.)
      -- list_conj = setFoldr1 (.&.)

setFoldr1 :: (a -> a -> a) -> Set.Set a -> a
setFoldr1 f s =
    case Set.minView s of
      Nothing -> error "setFoldr1"
      Just (x, s') -> Set.fold f x s'
