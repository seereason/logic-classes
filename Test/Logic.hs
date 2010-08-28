{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing -fno-warn-orphans #-}
module Test.Logic (tests) where

import qualified Data.Set as Set
import Data.String (IsString(fromString))
import Logic.Clause (Literal(..))
import qualified Logic.Instances.Native as P
import Logic.Logic (Logic(..), Boolean(..))
import Logic.Monad (runNormal)
import Logic.NormalForm (clauseNormalForm, clauseNormalForm)
import Logic.FirstOrder (Skolem(..), FirstOrderLogic(..), Term(..), showForm, freeVars, substitute)
import Logic.Satisfiable (theorem, inconsistant)
import PropLogic (PropForm(..), TruthTable, truthTable)
import qualified TextDisplay as TD
import Test.Types (V(..), AtomicFunction(..))
import Test.HUnit

-- |Don't use this at home!  It breaks type safety, fromString "True"
-- fromBool True.
instance Boolean String where
    fromBool = show

type TestFormula = P.Formula V String AtomicFunction

tests :: Test
tests = TestLabel "Logic" $ TestList (precTests ++ theoremTests)

formCase :: FirstOrderLogic (P.Formula V String AtomicFunction) (P.PTerm V AtomicFunction) V String AtomicFunction =>
            String -> TestFormula -> TestFormula -> Test
formCase s expected input = TestLabel s $ TestCase (assertEqual s expected input)

precTests :: [Test]
precTests =
    [ formCase "Logic - prec test 1"
               (a .&. (b .|. c))
               (a .&. b .|. c)
      -- You can't apply .~. without parens:
      -- :type (.~. a)   -> (FormulaPF -> t) -> t
      -- :type ((.~.) a) -> FormulaPF
    , formCase "Logic - prec test 2"
               (((.~.) a) .&. b)
               ((.~.) a .&. b)
    -- I switched the precedence of .&. and .|. from infixl to infixr to get
    -- some of the test cases to match the answers given on the miami.edu site,
    -- but maybe I should switch them back and adjust the answer given in the
    -- test case.
    , formCase "Logic - prec test 3"
               ((a .&. b) .&. c) -- infixl, with infixr we get (a .&. (b .&. c))
               (a .&. b .&. c)
    , TestCase (assertEqual "Logic - Find a free variable"
                (freeVars (for_all "x" (x .=. y) :: TestFormula))
                (Set.singleton "y"))
    , TestCase (assertEqual "Logic - Substitute a variable"
                (map sub
                         [ for_all "x" (x .=. y) {- :: Formula String String -}
                         , for_all "y" (x .=. y) {- :: Formula String String -} ])
                [ for_all "x" (x .=. z) :: TestFormula
                , for_all "y" (z .=. y) :: TestFormula ])
    ]
    where
      sub f = substitute (head . Set.toList . freeVars $ f) (var "z") f
      a = pApp ("a") []
      b = pApp ("b") []
      c = pApp ("c") []

x :: P.PTerm V AtomicFunction
x = var (fromString "x")
y :: P.PTerm V AtomicFunction
y = var (fromString "y")
z :: P.PTerm V AtomicFunction
z = var (fromString "z")

-- |Here is an example of automatic conversion from a FirstOrderLogic
-- instance to a PropositionalLogic instance.  The result is PropForm
-- a where a is the original type, but the a values will always be
-- "atomic" formulas, never the operators which can be converted into
-- the corresponding operator of a PropositionalLogic instance.
{-
test9a :: Test
test9a = TestCase 
           (assertEqual "Logic - convert to PropLogic"
            expected
            (flatten (cnf' (for_all "x" (for_all "y" (q [x, y] .<=>. for_all "z" (f [z, x] .<=>. f [z, y])))))))
    where
      f = pApp "f"
      q = pApp "q"
      expected :: PropForm TestFormula
      expected = CJ [DJ [N (A (pApp ("q") [var (V "x"),var (V "y")])),
                         N (A (pApp ("f") [var (V "z"),var (V "x")])),
                         A (pApp ("f") [var (V "z"),var (V "y")])],
                     DJ [N (A (pApp ("q") [var (V "x"),var (V "y")])),
                         N (A (pApp ("f") [var (V "z"),var (V "y")])),
                         A (pApp ("f") [var (V "z"),var (V "x")])],
                     DJ [A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")]),
                         A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")]),
                         A (pApp ("q") [var (V "x"),var (V "y")])],
                     DJ [N (A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")])),
                         A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")]),
                         A (pApp ("q") [var (V "x"),var (V "y")])],
                     DJ [A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")]),
                         N (A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")])),
                         A (pApp ("q") [var (V "x"),var (V "y")])],
                     DJ [N (A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")])),
                         N (A (pApp ("f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")])),
                         A (pApp ("q") [var (V "x"),var (V "y")])]]

moveQuantifiersOut1 :: Test
moveQuantifiersOut1 =
    formCase "Logic - moveQuantifiersOut1"
             (for_all "x2" ((pApp ("p") [var ("x2")]) .&. ((pApp ("q") [var ("x")]))))
             (prenexNormalForm (for_all "x" (pApp (fromString "p") [x]) .&. (pApp (fromString "q") [x])))

skolemize1 :: Test
skolemize1 =
    formCase "Logic - skolemize1" expected formula
    where
      expected :: TestFormula
      expected = for_all [V "y",V "z"] (for_all [V "v"] (pApp "P" [fApp (toSkolem 1) [], y, z, fApp ((toSkolem 2)) [y, z], v, fApp (toSkolem 3) [y, z, v]]))
      formula :: TestFormula
      formula = (snf' (exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w])))))))

skolemize2 :: Test
skolemize2 =
    formCase "Logic - skolemize2" expected formula
    where
      expected :: TestFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [],y])
      formula :: TestFormula
      formula = snf' (exists ["x"] (for_all ["y"] (pApp "loves" [x, y])))

skolemize3 :: Test
skolemize3 =
    formCase "Logic - skolemize3" expected formula
    where
      expected :: TestFormula
      expected = for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [y],y])
      formula :: TestFormula
      formula = snf' (for_all ["y"] (exists ["x"] (pApp "loves" [x, y])))
-}
{-
inf1 :: Test
inf1 =
    formCase "Logic - inf1" expected formula
    where
      expected :: TestFormula
      expected = ((pApp ("p") [var ("x")]) .=>. (((pApp ("q") [var ("x")]) .|. ((pApp ("r") [var ("x")])))))
      formula :: {- Implicative inf (C.Sentence V String AtomicFunction) (C.Term V AtomicFunction) V String AtomicFunction => -} TestFormula
      formula = convertFOF id id id (implicativeNormalForm (convertFOF id id id (for_all ["x"] (p [x] .=>. (q [x] .|. r [x]))) :: C.Sentence V String AtomicFunction) :: C.Sentence V String AtomicFunction)
-}

theoremTests :: [Test]
theoremTests =
    let s = pApp "S"
        h = pApp "H"
        m = pApp "M" in
    [ let formula = for_all "x" (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>.
                                  (s [x] .=>. m [x])) in
      TestCase (assertEqual "Logic - theorem test 1"
                (True,([],Just (CJ []),[([],True)]))
{-
                (True,
                 ([(pApp ("H") [var (V "x")]),(pApp ("M") [var (V "x")]),(pApp ("S") [var (V "x")])],
                  Just (CJ [DJ [A (pApp ("S") [var (V "x")]),
                                A (pApp ("H") [var (V "x")]),
                                N (A (pApp ("S") [var (V "x")])),
                                A (pApp ("M") [var (V "x")])],
                            DJ [N (A (pApp ("H") [var (V "x")])),
                                A (pApp ("H") [var (V "x")]),
                                N (A (pApp ("S") [var (V "x")])),
                                A (pApp ("M") [var (V "x")])],
                            DJ [A (pApp ("S") [var (V "x")]),
                                N (A (pApp ("M") [var (V "x")])),
                                N (A (pApp ("S") [var (V "x")])),
                                A (pApp ("M") [var (V "x")])],
                            DJ [N (A (pApp ("H") [var (V "x")])),
                                N (A (pApp ("M") [var (V "x")])),
                                N (A (pApp ("S") [var (V "x")])),
                                A (pApp ("M") [var (V "x")])]]),
                  [([False,False,False],True),
                   ([False,False,True],True),
                   ([False,True,False],True),
                   ([False,True,True],True),
                   ([True,False,False],True),
                   ([True,False,True],True),
                   ([True,True,False],True),
                   ([True,True,True],True)]))
-}
                (runNormal (theorem formula), table formula))
    , TestCase (assertEqual "Logic - theorem test 1a"
                (False,
                 False,
                 ([(pApp ("H") [fApp (toSkolem 1) []]),
                   (pApp ("M") [var ("y")]),
                   (pApp ("M") [fApp (toSkolem 1) []]),
                   (pApp ("S") [var ("y")]),
                   (pApp ("S") [fApp (toSkolem 1) []])],
                  Just (CJ [DJ [N (A (pApp ("H") [fApp (toSkolem 1) []])),
                                N (A (pApp ("M") [fApp (toSkolem 1) []])),
                                N (A (pApp ("S") [var ("y")])),
                                A (pApp ("M") [var ("y")])],
                            DJ [N (A (pApp ("M") [fApp (toSkolem 1) []])),
                                N (A (pApp ("S") [var ("y")])),
                                A (pApp ("M") [var ("y")]),
                                A (pApp ("S") [fApp (toSkolem 1) []])],
                            DJ [N (A (pApp ("S") [var ("y")])),
                                A (pApp ("H") [fApp (toSkolem 1) []]),
                                A (pApp ("M") [var ("y")]),
                                A (pApp ("S") [fApp (toSkolem 1) []])]]),
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
                 (runNormal (theorem formula), runNormal (inconsistant formula), table formula)))
                
    , TestCase (assertEqual "Logic - socrates is mortal, truth table"
                ([(pApp ("H") [var ("x")]),
                  (pApp ("M") [var ("x")]),
                  (pApp ("S") [var ("x")])]
                ,Just (CJ [DJ [N (A (pApp ("H") [var ("x")])),A (pApp ("M") [var ("x")])],
                           DJ [N (A (pApp ("S") [var ("x")])),A (pApp ("H") [var ("x")])],
                           DJ [N (A (pApp ("S") [var ("x")])),A (pApp ("M") [var ("x")])]]),
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
                         for_all "z" (s [z] .=>. m [z]))))

    , TestCase (assertEqual "Logic - socrates is not mortal"
                (False,
                 False,
                 ([(pApp ("H") [var ("x")]),
                   (pApp ("M") [var ("x")]),
                   (pApp ("S") [var ("x")]),
                   (pApp ("S") [fApp ("socrates") []])],
                  Just (CJ [DJ [N (A (pApp ("H") [var ("x")])),A (pApp ("M") [var ("x")])],
                            DJ [N (A (pApp ("M") [var ("x")])),N (A (pApp ("S") [var ("x")]))],
                            DJ [N (A (pApp ("S") [var ("x")])),A (pApp ("H") [var ("x")])],
                            DJ [A (pApp ("S") [fApp ("socrates") []])]]),
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
                 toSS [[((.~.) (pApp ("H") [var ("x")])),(pApp ("M") [var ("x")])],
                       [((.~.) (pApp ("M") [var ("x")])),((.~.) (pApp ("S") [var ("x")]))],
                       [((.~.) (pApp ("S") [var ("x")])),(pApp ("H") [var ("x")])],
                       [(pApp ("S") [fApp ("socrates") []])]])
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
                (let (formula :: TestFormula) =
                         for_all "x" ((s [x] .=>. h [x]) .&.
                                      (h [x] .=>. m [x]) .&.
                                      (m [x] .=>. ((.~.) (s [x])))) .&.
                         (s [fApp "socrates" []]) in
                 (runNormal (theorem formula), runNormal (inconsistant formula), table formula, runNormal (clauseNormalForm formula))))
    , let (formula :: TestFormula) =
              (for_all "x" (pApp "L" [var "x"] .=>. pApp "F" [var "x"]) .&. -- All logicians are funny
               exists "x" (pApp "L" [var "x"])) .=>.                            -- Someone is a logician
              (.~.) (exists "x" (pApp "F" [var "x"]))                           -- Someone / Nobody is funny
          input = table formula
          expected = ([(pApp ("F") [var ("x2")]),
                       (pApp ("F") [fApp (toSkolem 1) []]),
                       (pApp ("L") [var ("x")]),
                       (pApp ("L") [fApp (toSkolem 1) []])],
                      Just (CJ [DJ [N (A (pApp ("F") [var ("x2")])),N (A (pApp ("F") [fApp (toSkolem 1) []])),N (A (pApp ("L") [var ("x")]))],
                                DJ [N (A (pApp ("F") [var ("x2")])),N (A (pApp ("L") [var ("x")])),A (pApp ("L") [fApp (toSkolem 1) []])]]),
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
      in TestCase (assertEqual "Logic - gensler189" expected input)
    , let (formula :: TestFormula) =
              (for_all "x" (pApp "L" [var "x"] .=>. pApp "F" [var "x"]) .&. -- All logicians are funny
               exists "y" (pApp "L" [var (fromString "y")])) .=>.           -- Someone is a logician
              (.~.) (exists "z" (pApp "F" [var "z"]))                       -- Someone / Nobody is funny
          input = table formula
          expected = ([(pApp ("F") [var ("z")]),(pApp ("F") [fApp (toSkolem 1) []]),(pApp ("L") [var ("y")]),(pApp ("L") [fApp (toSkolem 1) []])],
                      Just (CJ [DJ [N (A (pApp ("F") [var ("z")])),N (A (pApp ("F") [fApp (toSkolem 1) []])),N (A (pApp ("L") [var ("y")]))],
                                DJ [N (A (pApp ("F") [var ("z")])),N (A (pApp ("L") [var ("y")])),A (pApp ("L") [fApp (toSkolem 1) []])]]),
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
      in TestCase (assertEqual "Logic - gensler189 renamed" expected input)
    ]

toSS :: Ord a => [[a]] -> Set.Set (Set.Set a)
toSS = Set.fromList . map Set.fromList

{-
theorem5 =
    TestCase (assertEqual "Logic - theorm test 2"
              (Just True)
              (theorem ((.~.) ((for_all "x" (((s [x] .=>. h [x]) .&.
                                               (h [x] .=>. m [x]))) .&.
                                exists "x" (s [x] .&.
                                             ((.~.) (m [x]))))))))
-}

instance TD.Display (TestFormula) where
    textFrame x = [showForm x]
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
    ( TestCase (assertEqual "Logic - truth table 1"
                (Just ["foo"])
                (prepare (for_all "x" (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))) >>=
                 return . TD.textFrame . truthTable)) )
    where s = pApp "S"
          h = pApp "H"
          m = pApp "M"

type FormulaPF = Formula String String
type F = PropForm FormulaPF

prepare :: FormulaPF -> F
prepare formula = ({- flatten . -} fromJust . toPropositional convertA . cnf . (.~.) $ formula)

convertA = Just . A
-}

table :: forall formula term v p f. (Literal formula, FirstOrderLogic formula term v p f, Ord formula, Skolem f, IsString v, Enum v, TD.Display formula) =>
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
      n f = (if inverted f then N . A . invert else A) $ f
