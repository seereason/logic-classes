{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing -fno-warn-orphans #-}
module Data.Logic.Tests.Logic (tests) where

import Data.Logic.Classes.Arity (Arity(arity))
import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Equals (AtomEq, (.=.), pApp, pApp1, showAtomEq, varAtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), showFirstOrder)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Negate (negated, (.~.))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Harrison.FOL (fv)
import Data.Logic.Harrison.Skolem (substituteEq)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (runNormal)
import Data.Logic.Satisfiable (theorem, inconsistant)
import Data.Logic.Tests.Common (TFormula, TTerm, myTest)
import qualified Data.Set as Set
import Data.String (IsString(fromString))
import PropLogic (PropForm(..), TruthTable, truthTable)
import qualified TextDisplay as TD
import Test.HUnit

-- |Don't use this at home!  It breaks type safety, fromString "True"
-- fromBool True.
instance Constants String where
    fromBool = show

tests :: Test
tests = TestLabel "Test.Logic" $ TestList (precTests ++ theoremTests)

{-
formCase :: (FirstOrderFormula TFormula TAtom V, AtomEq TAtom Pr TTerm, Term TTerm V AtomicFunction) =>
            String -> TFormula -> TFormula -> Test
formCase s expected input = TestLabel s $ TestCase (assertEqual s expected input)
-}

precTests :: [Test]
precTests =
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
    , TestCase (assertEqual "Logic - Find a free variable"
                (fv varAtomEq (for_all "x" (x .=. y) :: TFormula))
                (Set.singleton "y"))
    , TestCase (assertEqual "Logic - Substitute a variable"
                (map sub
                         [ for_all "x" (x .=. y) {- :: Formula String String -}
                         , for_all "y" (x .=. y) {- :: Formula String String -} ])
                [ for_all "x" (x .=. z) :: TFormula
                , for_all "y" (z .=. y) :: TFormula ])
    ]
    where
      sub f = substituteEq (head . Set.toList . fv varAtomEq $ f) (vt "z") f
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

x :: TTerm
x = vt (fromString "x")
y :: TTerm
y = vt (fromString "y")
z :: TTerm
z = vt (fromString "z")

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

instance Arity String where
    arity _ = Nothing

theoremTests :: [Test]
theoremTests =
    let s = pApp "S"
        h = pApp "H"
        m = pApp "M" in
    [ let formula = for_all "x" (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>.
                                  (s [x] .=>. m [x])) in
      myTest "Logic - theorem test 1"
                (True,([],Just (CJ []),[([],True)]))
{-
                (True,
                 ([(pApp ("H") [vt (V "x")]),(pApp ("M") [vt (V "x")]),(pApp ("S") [vt (V "x")])],
                  Just (CJ [DJ [A (pApp ("S") [vt (V "x")]),
                                A (pApp ("H") [vt (V "x")]),
                                N (A (pApp ("S") [vt (V "x")])),
                                A (pApp ("M") [vt (V "x")])],
                            DJ [N (A (pApp ("H") [vt (V "x")])),
                                A (pApp ("H") [vt (V "x")]),
                                N (A (pApp ("S") [vt (V "x")])),
                                A (pApp ("M") [vt (V "x")])],
                            DJ [A (pApp ("S") [vt (V "x")]),
                                N (A (pApp ("M") [vt (V "x")])),
                                N (A (pApp ("S") [vt (V "x")])),
                                A (pApp ("M") [vt (V "x")])],
                            DJ [N (A (pApp ("H") [vt (V "x")])),
                                N (A (pApp ("M") [vt (V "x")])),
                                N (A (pApp ("S") [vt (V "x")])),
                                A (pApp ("M") [vt (V "x")])]]),
                  [([False,False,False],True),
                   ([False,False,True],True),
                   ([False,True,False],True),
                   ([False,True,True],True),
                   ([True,False,False],True),
                   ([True,False,True],True),
                   ([True,True,False],True),
                   ([True,True,True],True)]))
-}
                (runNormal (theorem formula), table formula)
    , myTest "Logic - theorem test 1a"
                (False,
                 False,
                 ([(pApp1 ("H") (fApp (toSkolem 1) [])),
                   (pApp1 ("M") (vt ("y"))),
                   (pApp1 ("M") (fApp (toSkolem 1) [])),
                   (pApp1 ("S") (vt ("y"))),
                   (pApp1 ("S") (fApp (toSkolem 1) []))],
                  Just (CJ [DJ [A (pApp1 ("H") (fApp (toSkolem 1) [])),
                                A (pApp1 ("M") (vt ("y"))),
                                A (pApp1 ("S") (fApp (toSkolem 1) [])),
                                N (A (pApp1 ("S") (vt ("y"))))],
                            DJ [A (pApp1 ("M") (vt ("y"))),
                                A (pApp1 ("S") (fApp (toSkolem 1) [])),
                                N (A (pApp1 ("M") (fApp (toSkolem 1) []))),
                                N (A (pApp1 ("S") (vt ("y"))))],
                            DJ [A (pApp1 ("M") (vt ("y"))),
                                N (A (pApp1 ("H") (fApp (toSkolem 1) []))),
                                N (A (pApp1 ("M") (fApp (toSkolem 1) []))),
                                N (A (pApp1 ("S") (vt ("y"))))]]),
                  [([False,False,False,False,False],True),
                   ([False,False,False,False,True],True),
                   ([False,False,False,True,False],False),
                   ([False,False,False,True,True],True),
                   ([False,False,True,False,False],True),
                   ([False,False,True,False,True],True),
                   ([False,False,True,True,False],False),
                   ([False,False,True,True,True],True),
                   ([False,True,False,False,False],True),
                   ([False,True,False,False,True],True),
                   ([False,True,False,True,False],True),
                   ([False,True,False,True,True],True),
                   ([False,True,True,False,False],True),
                   ([False,True,True,False,True],True),
                   ([False,True,True,True,False],True),
                   ([False,True,True,True,True],True),
                   ([True,False,False,False,False],True),
                   ([True,False,False,False,True],True),
                   ([True,False,False,True,False],True),
                   ([True,False,False,True,True],True),
                   ([True,False,True,False,False],True),
                   ([True,False,True,False,True],True),
                   ([True,False,True,True,False],False),
                   ([True,False,True,True,True],False),
                   ([True,True,False,False,False],True),
                   ([True,True,False,False,True],True),
                   ([True,True,False,True,False],True),
                   ([True,True,False,True,True],True),
                   ([True,True,True,False,False],True),
                   ([True,True,True,False,True],True),
                   ([True,True,True,True,False],True),
                   ([True,True,True,True,True],True)]))
                
                (let formula = (for_all "x" ((s [x] .=>. h [x]) .&. (h [x] .=>. m [x]))) .=>.
                               (for_all "y" (s [y] .=>. m [y])) in
                 (runNormal (theorem formula), runNormal (inconsistant formula), table formula))
                
    , myTest "Logic - socrates is mortal, truth table"
                ([(pApp1 ("H") (vt ("x"))),
                  (pApp1 ("M") (vt ("x"))),
                  (pApp1 ("S") (vt ("x")))],
                 Just (CJ [DJ [A (pApp1 ("H") (vt ("x"))),N (A (pApp1 ("S") (vt ("x"))))],
                           DJ [A (pApp1 ("M") (vt ("x"))),N (A (pApp1 ("H") (vt ("x"))))],
                           DJ [A (pApp1 ("M") (vt ("x"))),N (A (pApp1 ("S") (vt ("x"))))]]),
                 [([False,False,False],True),
                  ([False,False,True],False),
                  ([False,True,False],True),
                  ([False,True,True],False),
                  ([True,False,False],False),
                  ([True,False,True],False),
                  ([True,True,False],True),
                  ([True,True,True],True)])
                -- This formula has separate variables for each of the
                -- three beliefs.  To combine these into an argument
                -- we would wrap a single exists around them all and
                -- remove the existing ones, substituting that one
                -- variable into each formula.
                (table (for_all "x" (s [x] .=>. h [x]) .&.
                         for_all "y" (h [y] .=>. m [y]) .&.
                         for_all "z" (s [z] .=>. m [z])))

    , myTest "Logic - socrates is not mortal"
                (False,
                 False,
                 ([(pApp ("H") [vt ("x")]),
                   (pApp ("M") [vt ("x")]),
                   (pApp ("S") [vt ("x")]),
                   (pApp ("S") [fApp ("socrates") []])],
                  Just (CJ [DJ [A (pApp ("H") [vt ("x")]),N (A (pApp ("S") [vt ("x")]))],
                            DJ [A (pApp ("M") [vt ("x")]),N (A (pApp ("H") [vt ("x")]))],
                            DJ [A (pApp ("S") [fApp ("socrates") []])],
                            DJ [N (A (pApp ("M") [vt ("x")])),N (A (pApp ("S") [vt ("x")]))]]),
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
                   ([True,True,True,True],False)]),
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
                (let (formula :: TFormula) =
                         for_all "x" ((s [x] .=>. h [x]) .&.
                                      (h [x] .=>. m [x]) .&.
                                      (m [x] .=>. ((.~.) (s [x])))) .&.
                         (s [fApp "socrates" []]) in
                 (runNormal (theorem formula), runNormal (inconsistant formula), table formula, runNormal (clauseNormalForm formula) :: Set.Set (Set.Set TFormula)))
    , let (formula :: TFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "x" (pApp "L" [vt "x"])) .=>.                            -- Someone is a logician
              (.~.) (exists "x" (pApp "F" [vt "x"]))                           -- Someone / Nobody is funny
          input = table formula
          expected = ([(pApp ("F") [vt ("x2")]),
                       (pApp ("F") [fApp (toSkolem 1) []]),
                       (pApp ("L") [vt ("x")]),
                       (pApp ("L") [fApp (toSkolem 1) []])],
                      Just (CJ [DJ [A (pApp1 ("L") (fApp (toSkolem 1) [])),N (A (pApp1 ("F") (vt ("x2")))),N (A (pApp1 ("L") (vt ("x"))))],
                                DJ [N (A (pApp1 ("F") (vt ("x2")))),N (A (pApp1 ("F") (fApp (toSkolem 1) []))),N (A (pApp1 ("L") (vt ("x"))))]]),
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
                       ([True,True,True,True],False)])
      in myTest "Logic - gensler189" expected input
    , let (formula :: TFormula) =
              (for_all "x" (pApp "L" [vt "x"] .=>. pApp "F" [vt "x"]) .&. -- All logicians are funny
               exists "y" (pApp "L" [vt (fromString "y")])) .=>.           -- Someone is a logician
              (.~.) (exists "z" (pApp "F" [vt "z"]))                       -- Someone / Nobody is funny
          input = table formula
          expected :: TruthTable TFormula
          expected = ([(pApp1 ("F") (vt ("z"))),(pApp1 ("F") (fApp (toSkolem 1) [])),(pApp1 ("L") (vt ("y"))),(pApp1 ("L") (fApp (toSkolem 1) []))],Just (CJ [DJ [A (pApp1 ("L") (fApp (toSkolem 1) [])),N (A (pApp1 ("F") (vt ("z")))),N (A (pApp1 ("L") (vt ("y"))))],DJ [N (A (pApp1 ("F") (vt ("z")))),N (A (pApp1 ("F") (fApp (toSkolem 1) []))),N (A (pApp1 ("L") (vt ("y"))))]]),[([False,False,False,False],True),([False,False,False,True],True),([False,False,True,False],True),([False,False,True,True],True),([False,True,False,False],True),([False,True,False,True],True),([False,True,True,False],True),([False,True,True,True],True),([True,False,False,False],True),([True,False,False,True],True),([True,False,True,False],False),([True,False,True,True],True),([True,True,False,False],True),([True,True,False,True],True),([True,True,True,False],False),([True,True,True,True],False)])
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

table :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal formula atom v,
                                     Ord formula, Skolem f, IsString v, Variable v, TD.Display formula, Constants p, Eq p) =>
         formula -> TruthTable formula
table f =
    -- truthTable :: Ord a => PropForm a -> TruthTable a
    tt cnf'
    where
      tt :: PropForm formula -> TruthTable formula
      tt = truthTable
      cnf' :: PropForm formula
      cnf' = CJ (map (DJ . map n) cnf)
      cnf :: [[formula]]
      cnf = fromSS (runNormal (clauseNormalForm f))
      fromSS = map Set.toList . Set.toList
      n f = (if negated f then N . A . (.~.) else A) $ f
