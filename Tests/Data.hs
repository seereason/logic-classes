{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, MonoLocalBinds, NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeFamilies  #-}
{-# OPTIONS -fno-warn-name-shadowing #-}
module Data
    ( tests
    , allFormulas
    , proofs
{-
    , formulas
    , animalKB
    , animalConjectures
    , chang43KB
    , chang43Conjecture
    , chang43ConjectureRenamed
-}
    ) where

import Common (TestFormula(..), TestProof(..), Expected(..), ProofExpected(..), doTest, doProof, TTestProof)
import Data.Boolean (Literal(..))
import Data.Logic.ATP.Apply (HasApply(TermOf, PredOf), pApp, Predicate)
import Data.Logic.ATP.Equate ((.=.), HasEquate)
import Data.Logic.ATP.Formulas (false, IsFormula(AtomOf), true)
import Data.Logic.ATP.Lit ((.~.), IsLiteral)
import Data.Logic.ATP.Prop (IsPropositional(..))
import Data.Logic.ATP.Quantified (IsQuantified(..), for_all, exists)
import Data.Logic.ATP.Skolem (HasSkolem(toSkolem), Formula, SkAtom, SkTerm, Function)
import Data.Logic.ATP.Term (IsTerm(..), V)
import qualified Data.Logic.Instances.Chiou as C
import Data.Logic.KnowledgeBase (WithId(WithId, wiItem, wiIdent), Proof(..), ProofResult(..))
import Data.Logic.Normal.Implicative (ImplicativeForm(INF), makeINF')
import Data.Map as Map (fromList)
import Data.Set as Set (Set, fromList, toList)
import Data.String (IsString)
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (prettyShow)

-- |for_all with a list of variables, for backwards compatibility.
for_all' :: IsQuantified formula => [VarOf formula] -> formula -> formula
for_all' vs f = foldr for_all f vs

-- |exists with a list of variables, for backwards compatibility.
exists' :: IsQuantified formula => [VarOf formula] -> formula -> formula
exists' vs f = foldr for_all f vs

pApp2 :: (atom ~ AtomOf formula, term ~ TermOf atom, p ~ PredOf atom,
          IsFormula formula, HasApply atom) => p -> term -> term -> formula
pApp2 p a b = pApp p [a, b]

{-
:m +Data.Logic.Test
:m +Data.Logic.Types.FirstOrder
:m +Data.Set
runNormal (clauseNormalForm (true :: Formula V Predicate Function)) :: Set (Set (Formula V Predicate Function))
runNormal (skolemNormalForm (true :: Formula V Predicate Function)) :: Formula V Predicate Function
:m +Data.Logic.Normal.Prenex
prenexNormalForm true :: Formula V Predicate Function
:m +Data.Logic.Normal.Skolem
:m +Data.Logic.Normal.Negation
-}

tests :: [Test] -> [TTestProof] -> Test
tests fs ps =
    TestLabel "Tests.Data" $ TestList (fs ++ map doProof ps)

allFormulas :: [Test]
allFormulas = (formulas ++
               map doTest (concatMap snd [animalKB, chang43KB]) ++
               animalConjectures ++
               [chang43Conjecture, chang43ConjectureRenamed])

formulas :: [Test]
formulas =
    let n = (.~.)
        p = pApp "p"
        q = pApp "q"
        r = pApp "r"
        s = pApp "s"
        t = pApp "t"
        p0 = p []
        q0 = q []
        r0 = r []
        s0 = s []
        t0 = t []
        (x, y, z, u, v, w) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "z" :: SkTerm, vt "u" :: SkTerm, vt "v" :: SkTerm, vt "w" :: SkTerm)
        z2 = vt "z'" :: SkTerm in
    [ doTest $
      TestFormula
      { formula = p0 .|. q0 .&. r0 .|. n s0 .&. n t0
      , name = "operator precedence"
      , expected = [ FirstOrderFormula (p0 .|. (q0 .&. r0) .|. ((n s0) .&. (n t0))) ] }
    , doTest $
      TestFormula
      { formula = true
      , name = "True"
      , expected = [ClauseNormalForm  (toSS [[]])] }
    , doTest $
      TestFormula
      { formula = false
      , name = "False"
      , expected = [ClauseNormalForm  (toSS [])] }
    , doTest $
      TestFormula
      { formula = true
      , name = "True"
      , expected = [DisjNormalForm  (toSS [[]])] } -- Make sure these are right
    , doTest $
      TestFormula
      { formula = false
      , name = "False"
      , expected = [DisjNormalForm  (toSS [])] }
    , doTest $
      TestFormula
      { formula = pApp "p" []
      , name = "p"
      , expected = [ClauseNormalForm  (toSS [[pApp "p" []]])] }
    , let p = pApp "p" [] in
      doTest $
      TestFormula
      { formula = p .&. ((.~.) (p))
      , name = "p&~p"
      , expected = [ PrenexNormalForm ((pApp ("p") []) .&. (((.~.) (pApp ("p") []))))
                   , ClauseNormalForm (toSS [[(p)], [((.~.) (p))]])
                   ] }
    , doTest $
      TestFormula
      { formula = pApp "p" [vt "x"]
      , name = "p[x]"
      , expected = [ClauseNormalForm  (toSS [[pApp "p" [x]]])] }
    , let f = pApp "f"
          q = pApp "q" in
      doTest $
      TestFormula
      { name = "iff"
      , formula = for_all "x" (for_all "y" (q [x, y] .<=>. for_all "z" (f [z, x] .<=>. f [z, y])))
      , expected = [ PrenexNormalForm
                     (for_all "x"
                      (for_all "y"
                       (for_all "z"
                        (exists "z'"
                         (((((q [x,y])) .&.
                            ((((((f [z,x])) .&.
                                ((f [z,y])))) .|.
                              (((((.~.) (f [z,x]))) .&.
                                (((.~.) (f [z,y]))))))))) .|.
                          (((((.~.) (q [x,y]))) .&.
                            ((((((f [z2,x])) .&.
                                (((.~.) (f [z2,y]))))) .|.
                              (((((.~.) (f [z2,x]))) .&.
                                ((f [z2,y])))))))))))))
                   , ClauseNormalForm
                     (toSS [[(pApp2 ("f") (vt ("z")) (vt ("x"))),
                             (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                             (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y"))))],
                            [(pApp2 ("f") (vt ("z")) (vt ("x"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y")))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))],
                            [(pApp2 ("f") (vt ("z")) (vt ("x"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y")))),
                             ((.~.) (pApp2 ("q") (vt ("x")) (vt ("y"))))],
                            [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                             (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                             (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("x"))))],
                            [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("x")))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))],
                            [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                             ((.~.) (pApp2 ("f") (vt ("z")) (vt ("x")))),
                             ((.~.) (pApp2 ("q") (vt ("x")) (vt ("y"))))],
                            [(pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                             (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),
                             (pApp2 ("q") (vt ("x")) (vt ("y")))],
                            [(pApp2 ("q") (vt ("x")) (vt ("y"))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                             ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))]])
                   ]
      }
    , doTest $
      TestFormula
      { name = "move quantifiers out"
      , formula = (for_all "x" (pApp "p" [x]) .&. (pApp "q" [x]))
      , expected = [PrenexNormalForm (for_all "x'" ((pApp "p" [vt ("x'")]) .&. ((pApp "q" [vt ("x")]))))]
      }
    , doTest $
      TestFormula
      { name = "skolemize2"
      , formula = exists "x" (for_all "y" (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (pApp ("loves") [fApp (toSkolem "x" 1) [],y])]
      }
    , doTest $
      TestFormula
      { name = "skolemize3"
      , formula = for_all "y" (exists "x" (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (pApp ("loves") [fApp (toSkolem "x" 1) [y],y])]
      }
    , doTest $
      TestFormula
      { formula = exists "x" (for_all' ["y", "z"]
                              (exists "u"
                               (for_all "v"
                                (exists "w"
                                 (pApp "P" [x, y, z, u, v, w])))))
      , name = "chang example 4.1"
      , expected = [ SkolemNormalForm (pApp "P" [fApp (toSkolem "x" 1) [],
                                                 vt ("y"),
                                                 vt ("z"),
                                                 fApp (toSkolem "u" 1) [vt ("y"),vt ("z")],
                                                 vt ("v"),
                                                 fApp (toSkolem "w" 1) [vt ("v"), vt ("y"),vt ("z")]]) ]
      }
    , doTest $
      TestFormula
      { name = "chang example 4.2"
      -- ∀x ∃y∃z ~P(x,y) & Q(x,z) | R(x,y,z)
      , formula = for_all "x" (exists' ["y", "z"] (((((.~.) (pApp "P" [x, y])) .&. pApp "Q" [x, z]) .|. pApp "R" [x, y, z])))
      -- ∀x ~P(x,Sk1[x]) | R(x,Sk1[x],Sk2[x]) & Q(x,Sk2[x]) | R(x,Sk1[x],Sk2[x])
      , expected = [ SkolemNormalForm
                     ((((.~.) (pApp ("P") [vt ("x"),vt ("y")])) .&.
                       ((pApp ("Q") [vt ("x"),vt ("z")]))) .|.
                      ((pApp ("R") [vt ("x"),vt ("y"),vt ("z")])))
                   , ClauseNormalForm
                     (toSS
                      [[((.~.) (pApp ("P") [vt ("x"),vt ("y")])),
                       (pApp ("R") [vt ("x"),vt ("y"),vt ("z")])],
                      [(pApp ("Q") [vt ("x"),vt ("z")]),
                       (pApp ("R") [vt ("x"),vt ("y"),vt ("z")])]]) ]
      }
    , doTest $
      TestFormula
      { formula = n p0 .|. q0 .&. p0 .|. r0 .&. n q0 .&. n r0
      , name = "chang 7.2.1a - unsat"
      , expected = [ SatSolverSat False ] }
    , doTest $
      TestFormula
      { formula = p0 .|. q0 .|. r0 .&. n p0 .&. n q0 .&. n r0 .|. s0 .&. n s0
      , name = "chang 7.2.1b - unsat"
      , expected = [ SatSolverSat False ] }
    , doTest $
      TestFormula
      { formula = p0 .|. q0 .&. q0 .|. r0 .&. r0 .|. s0 .&. n r0 .|. n p0 .&. n s0 .|. n q0 .&. n q0 .|. n r0
      , name = "chang 7.2.1c - unsat"
      , expected = [ SatSolverSat False ] }
    , let q = pApp "q"
          f = pApp "f"
          sk1 = f [fApp (toSkolem "x" 1) [x,x,y,z],y]
          sk2 = f [fApp (toSkolem "x" 1) [x,x,y,z],x] in
      doTest $
      TestFormula
      { name = "distribute bug test"
      , formula = ((((.~.) (q [x,y])) .|.
                    ((((.~.) (sk2)) .|. (sk1)) .&.
                     (((.~.) (sk1)) .|. (sk2)))) .&.
                   ((((sk2) .&.
                      ((.~.) (sk1))) .|. ((sk1) .&.
                      ((.~.) (sk2)))) .|. (q [x,y])))
      , expected = [ClauseNormalForm
                    (toSS
                     [[sk2,sk1,pApp ("q") [x,y]],
                      [sk2,((.~.) (sk1)),((.~.) (q [x,y]))],
                      [sk1,((.~.) (sk2)),((.~.) (q [x,y]))],
                      [q [x,y], ((.~.) sk2),((.~.) sk1)]])]
      }
    , let x = vt "x" :: SkTerm
          y = vt "y" :: SkTerm
          x' = vt "x" :: C.CTerm V Function
          y' = vt "y" :: C.CTerm V Function in
      doTest $
      TestFormula
      { name = "convert to Chiou 1"
      , formula = exists "x" (x .=. y)
      , expected = [ConvertToChiou (exists "x" (x' .=. y') :: C.Sentence V Predicate Function)]
      }
    , let s = pApp "s"
          s' = pApp "s"
          x' = vt "x"
          y' = vt "y" in
      doTest $
      TestFormula
      { name = "convert to Chiou 2"
      , formula = s [fApp ("a") [x, y]]
      , expected = [ConvertToChiou (s' [fApp "a" [x', y']])]
      }
    , let s = pApp "s"
          h = pApp "h"
          m = pApp "m"
          s' = pApp "s"
          h' = pApp "h"
          m' = pApp "m"
          x' = vt "x" in
      doTest $
      TestFormula
      { name = "convert to Chiou 3"
      , formula = for_all "x" (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
      , expected = [ConvertToChiou (for_all "x" (((s' [x'] .=>. h' [x']) .&. (h' [x'] .=>. m' [x'])) .=>. (s' [x'] .=>. m' [x'])))]
      }
    , let taller a b = pApp "taller" [a, b]
          wise a = pApp "wise" [a] in
      doTest $
      TestFormula
      { name = "cnf test 1"
      , formula = for_all "y" (for_all "x" (taller y x .|. wise x) .=>. wise y)
      , expected = [ClauseNormalForm
                    (toSS
                     [[(pApp ("wise") [vt ("y")]),
                       ((.~.) (pApp ("taller") [vt ("y"),fApp (toSkolem "x" 1) [vt ("y")]]))],
                      [(pApp ("wise") [vt ("y")]),
                       ((.~.) (pApp ("wise") [fApp (toSkolem "x" 1) [vt ("y")]]))]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 2"
      , formula = ((.~.) (exists "x" (pApp "s" [x] .&. pApp "q" [x])))
      , expected = [ ClauseNormalForm (toSS
                                       [[((.~.) (pApp ("q") [vt ("x")])),
                                         ((.~.) (pApp ("s") [vt ("x")]))]])
                   , PrenexNormalForm (for_all "x"
                                       (((.~.) (pApp ("s") [vt ("x")])) .|.
                                        (((.~.) (pApp ("q") [vt ("x")])))))
                                     {- [[((.~.) (pApp "s" [vt "x"])),
                                        ((.~.) (pApp "q" [vt "x"]))]] -}
                   ]
      }
    , doTest $
      TestFormula
      { name = "cnf test 3"
      , formula = (for_all "x" (p [x] .=>. (q [x] .|. r [x])))
      , expected = [ClauseNormalForm (toSS [[((.~.) (pApp "p" [vt "x"])),(pApp "q" [vt "x"]),(pApp "r" [vt "x"])]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 4"
      , formula = ((.~.) (exists "x" (p [x] .=>. exists "y" (q [y]))))
      , expected = [ClauseNormalForm (toSS [[(pApp "p" [vt "x"])],[((.~.) (pApp "q" [vt "y"]))]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 5"
      , formula = (for_all "x" (q [x] .|. r [x] .=>. s [x]))
      , expected = [ClauseNormalForm (toSS [[((.~.) (pApp "q" [vt "x"])),(pApp "s" [vt "x"])],[((.~.) (pApp "r" [vt "x"])),(pApp "s" [vt "x"])]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 6"
      , formula = (exists "x" (p0 .=>. pApp "f" [x]))
      , expected = [ClauseNormalForm (toSS [[((.~.) (pApp "p" [])),(pApp "f" [fApp (toSkolem "x" 1) []])]])]
      }
    , let p = pApp "p" []
          f' = pApp "f" [x]
          f = pApp "f" [fApp (toSkolem "x" 1) []] in
      doTest $
      TestFormula
      { name = "cnf test 7"
      , formula = exists "x" (p .<=>. f')
      , expected = [ PrenexNormalForm (exists "x" ((p .&. f') .|. ((((.~.) p) .&. (((.~.) f'))))))
                   , SkolemNormalForm ((p .&. f) .|. (((.~.) p) .&. (((.~.) f))))
                   , TrivialClauses [(False,Set.fromList [((.~.) (pApp ("p") [])),(pApp ("f") [fApp (toSkolem "x" 1) []])]),
                                     (False,Set.fromList [((.~.) (pApp ("f") [fApp (toSkolem "x" 1) []])),(pApp ("p") [])])]
                   , ClauseNormalForm (toSS [[(f), ((.~.) p)], [p, ((.~.) f)]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 8"
      , formula = (for_all "z" (exists "y" (for_all "x" (pApp "f" [x, y] .<=>. (pApp "f" [x, z] .&. ((.~.) (pApp "f" [x, x])))))))
      , expected = [ClauseNormalForm
                    (toSS [[((.~.) (pApp "f" [vt "x",fApp (toSkolem "y" 1) [vt "z"]])),(pApp "f" [vt "x",vt "z"])],
                           [((.~.) (pApp "f" [vt "x",fApp (toSkolem "y" 1) [vt "z"]])),((.~.) (pApp "f" [vt "x",vt "x"]))],
                           [((.~.) (pApp "f" [vt "x",vt "z"])),(pApp "f" [vt "x",vt "x"]),(pApp "f" [vt "x",fApp (toSkolem "y" 1) [vt "z"]])]])]
      }
    , let f = pApp "f"
          q = pApp "q"
          (x, y, z) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "z" :: SkTerm) in
      doTest $
      TestFormula
      { name = "cnf test 9"
      , formula = (for_all "x" (for_all "x" (for_all "y" (q [x, y] .<=>. for_all "z" (f [z, x] .<=>. f [z, y])))))
      , expected = [ClauseNormalForm
                    (toSS
                     [[(pApp2 ("f") (vt ("z")) (vt ("x"))),
                       (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                       (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),
                       ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y"))))],
                      [(pApp2 ("f") (vt ("z")) (vt ("x"))),
                       ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y")))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))],
                      [(pApp2 ("f") (vt ("z")) (vt ("x"))),
                       ((.~.) (pApp2 ("f") (vt ("z")) (vt ("y")))),
                       ((.~.) (pApp2 ("q") (vt ("x")) (vt ("y"))))],
                      [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                       (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                       (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),((.~.) (pApp2 ("f") (vt ("z")) (vt ("x"))))],
                      [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                       ((.~.) (pApp2 ("f") (vt ("z")) (vt ("x")))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))],
                      [(pApp2 ("f") (vt ("z")) (vt ("y"))),
                       ((.~.) (pApp2 ("f") (vt ("z")) (vt ("x")))),
                       ((.~.) (pApp2 ("q") (vt ("x")) (vt ("y"))))],
                      [(pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x"))),
                       (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))),
                       (pApp2 ("q") (vt ("x")) (vt ("y")))],
                      [(pApp2 ("q") (vt ("x")) (vt ("y"))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("x")))),
                       ((.~.) (pApp2 ("f") (fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]) (vt ("y"))))]])
                   ]
      }
    , doTest $
      TestFormula
      { name = "cnf test 10"
      , formula = (for_all "x" (exists "y" ((for_all "x" (exists "z" (q [y, x, z]) .=>. r [y]) .=>. p [x, y]))))
      , expected = [ClauseNormalForm
                    (toSS
                     [[(pApp ("p") [vt ("x"),fApp (toSkolem "y" 1) [vt ("x")]]),
                       (pApp ("q") [fApp (toSkolem "y" 1) [vt "x"],fApp (toSkolem "x'" 1) [vt "x"],fApp (toSkolem "z" 1) [vt "x"]])],
                      [(pApp ("p") [vt ("x"),fApp (toSkolem "y" 1) [vt ("x")]]),
                       ((.~.) (pApp ("r") [fApp (toSkolem "y" 1) [vt "x"]]))]])
                   ]
      }
    , doTest $
      TestFormula
      { name = "cnf test 11"
      , formula = (for_all "x" (for_all "z" (p [x, z] .=>. exists "y" ((.~.) (q [x, y] .|. ((.~.) (r [y, z])))))))
      , expected = [ClauseNormalForm
                    (toSS
                    [[((.~.) (pApp "p" [vt "x",vt "z"])),((.~.) (pApp "q" [vt "x",fApp (toSkolem "y" 1) [vt "x",vt "z"]]))],
                     [((.~.) (pApp "p" [vt "x",vt "z"])),(pApp "r" [fApp (toSkolem "y" 1) [vt "x",vt "z"],vt "z"])]])]
      }
    , doTest $
      TestFormula
      { name = "cnf test 12"
      , formula = ((p0 .=>. q0) .=>. (((.~.) r0) .=>. (s0 .&. t0)))
      , expected = [ClauseNormalForm
                    (toSS
                    [[(pApp "p" []),(pApp "r" []),(pApp "s" [])],
                     [((.~.) (pApp "q" [])),(pApp "r" []),(pApp "s" [])],
                     [(pApp "p" []),(pApp "r" []),(pApp "t" [])],
                     [((.~.) (pApp "q" [])),(pApp "r" []),(pApp "t" [])]])]
      }
    , let (f :: Formula) = for_all "x" ( x .=. x) .=>. for_all "x" (exists "y" ((x .=. y))) in
      doTest $
      TestFormula
      { name = "cnf test 13 " ++ prettyShow f
      , formula = f
        -- [[x = sKy[x], ¬sKx[] = sKx[]]]
      , expected = [ClauseNormalForm (toSS [[x .=. fApp (toSkolem "y" 1) [x], (.~.) (fApp (toSkolem "x" 1) [] .=. fApp (toSkolem "x" 1) [])]])]
      }
    , let p = pApp "p" [] in
      doTest $
      TestFormula
      { name = "psimplify 50"
      , formula = true .=>. (p .<=>. (p .<=>. false))
      , expected = [ SimplifiedForm (p .<=>. (.~.) p) ] }
    , doTest $
      TestFormula
      { name = "psimplify 51"
      , formula = (((pApp "x" [] .=>. pApp "y" []) .=>. true) .|. false)
      , expected = [ SimplifiedForm true ] }
    , let q = pApp "q" [] in
      doTest $
      TestFormula
      { name = "simplify 140.3"
      , formula = (for_all "x"
                   (for_all "y"
                    (pApp "p" [vt "x"] .|. (pApp "p" [vt "y"] .&. false))) .=>.
                   (exists "z" q))
      , expected = [ SimplifiedForm ((for_all "x" (pApp "p" [vt "x"])) .=>.
                                        (pApp "q" [])) ] }
    , doTest $
      TestFormula
      { name = "nnf 141.1"
      , formula = ((for_all "x" (pApp "p" [vt "x"])) .=>. ((exists "y" (pApp "q" [vt "y"])) .<=>. (exists "z" (pApp "p" [vt "z"] .&. pApp "q" [vt "z"]))))
      , expected = [ NegationNormalForm
                     ((exists "x" ((.~.) (pApp "p" [vt "x"]))) .|.
                      ((((exists "y" (pApp "q" [vt "y"])) .&. ((exists "z" ((pApp "p" [vt "z"]) .&. ((pApp "q" [vt "z"])))))) .|.
                        (((for_all "y" ((.~.) (pApp "q" [vt "y"]))) .&.
                          ((for_all "z" (((.~.) (pApp "p" [vt "z"])) .|. (((.~.) (pApp "q" [vt "z"]))))))))))) ] }
    , doTest $
      TestFormula
      { name = "pnf 144.1"
      , formula = (for_all "x" (pApp "p" [vt "x"] .|. pApp "r" [vt "y"]) .=>.
                   (exists "y" (exists "z" (pApp "q" [vt "y"] .|. ((.~.) (exists "z" (pApp "p" [vt "z"] .&. pApp "q" [vt "z"])))))))
      , expected = [ PrenexNormalForm
                     (exists "x"
                      (for_all "z"
                       ((((.~.) (pApp "p" [vt "x"])) .&. (((.~.) (pApp "r" [vt "y"])))) .|.
                        (((pApp "q" [vt "x"]) .|. ((((.~.) (pApp "p" [vt "z"])) .|. (((.~.) (pApp "q" [vt "z"])))))))))) ] }
    , let (x, y, u, v) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "u" :: SkTerm, vt "v" :: SkTerm)
          fv = fApp (toSkolem "v" 1) [u,x]
          fy = fApp (toSkolem "y" 1) [x] in
      doTest $
      TestFormula
      { name = "snf 150.1"
      , formula = (exists "y" (pApp "<" [x, y] .=>. for_all "u" (exists "v" (pApp "<" [fApp "*" [x, u], fApp "*" [y, v]]))))
      , expected = [ SkolemNormalForm (((.~.) (pApp "<" [x, fy])) .|. pApp "<" [fApp "*" [x, u], fApp "*" [fy, fv]]) ] }
    , let p x = pApp "p" [x]
          q x = pApp "q" [x]
          (x, y, z) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "z" :: SkTerm) in
      doTest $
      TestFormula
      { name = "snf 150.2"
      , formula = (for_all "x" (p x .=>. (exists "y" (exists "z" (q y .|. (.~.) (exists "z" (p z .&. (q z))))))))
      , expected = [ SkolemNormalForm (((.~.) (p x)) .|. (q (fApp (toSkolem "y" 1) []) .|. (((.~.) (p z)) .|. ((.~.) (q z))))) ] }
    ]

animalKB :: (String, [TestFormula Formula SkAtom V])
animalKB =
    let x = vt "x"
        y = vt "y"
        dog = pApp "Dog"
        cat = pApp "Cat"
        owns = pApp "Owns"
        kills = pApp "Kills"
        animal = pApp "Animal"
        animalLover = pApp "AnimalLover"
        jack = fApp "Jack" []
        tuna = fApp "Tuna" []
        curiosity = fApp "Curiosity" [] in
    ("animal"
    , [ TestFormula
       { formula = exists "x" (dog [x] .&. owns [jack, x]) -- [[Pos 1],[Pos 2]]
       , name = "jack owns a dog"
       , expected = [ClauseNormalForm (toSS [[(pApp "Dog" [fApp (toSkolem "x" 1) []])],[(pApp "Owns" [fApp "Jack" [],fApp (toSkolem "x" 1) []])]])]
       -- owns(jack,sK0)
       -- dog (SK0)
                   }
     , TestFormula
       { formula = for_all "x" ((exists "y" (dog [y] .&. (owns [x, y]))) .=>. (animalLover [x])) -- [[Neg 1,Neg 2,Pos 3]]
       , name = "dog owners are animal lovers"
       , expected = [ PrenexNormalForm (for_all "x" (for_all "y" ((((.~.) (pApp "Dog" [vt "y"])) .|.
                                                                           (((.~.) (pApp "Owns" [vt "x",vt "y"])))) .|.
                                                                          ((pApp "AnimalLover" [vt "x"])))))
                    , ClauseNormalForm (toSS [[((.~.) (pApp "Dog" [vt "y"])),((.~.) (pApp "Owns" [vt "x",vt "y"])),(pApp "AnimalLover" [vt "x"])]]) ]
       -- animalLover(X0) | ~owns(X0,sK1(X0)) | ~dog(sK1(X0))
       }
     , TestFormula
       { formula = for_all "x" (animalLover [x] .=>. (for_all "y" ((animal [y]) .=>. ((.~.) (kills [x, y]))))) -- [[Neg 3,Neg 4,Neg 5]]
       , name = "animal lovers don't kill animals"
       , expected = [ClauseNormalForm  (toSS [[((.~.) (pApp "AnimalLover" [vt "x"])),((.~.) (pApp "Animal" [vt "y"])),((.~.) (pApp "Kills" [vt "x",vt "y"]))]])]
       -- ~kills(X0,X2) | ~animal(X2) | ~animalLover(sK2(X0))
       }
     , TestFormula
       { formula = (kills [jack, tuna]) .|. (kills [curiosity, tuna]) -- [[Pos 5,Pos 5]]
       , name = "Either jack or curiosity kills tuna"
       , expected = [ClauseNormalForm  (toSS [[(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []]),(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []])]])]
       -- kills(curiosity,tuna) | kills(jack,tuna)
       }
     , TestFormula
       { formula = cat [tuna] -- [[Pos 6]]
       , name = "tuna is a cat"
       , expected = [ClauseNormalForm  (toSS [[(pApp "Cat" [fApp "Tuna" []])]])]
       -- cat(tuna)
       }
     , TestFormula
       { formula = for_all "x" ((cat [x]) .=>. (animal [x])) -- [[Neg 6,Pos 4]]
       , name = "a cat is an animal"
       , expected = [ClauseNormalForm  (toSS [[((.~.) (pApp "Cat" [vt "x"])),(pApp "Animal" [vt "x"])]])]
       -- animal(X0) | ~cat(X0)
       }
     ])

animalConjectures :: [Test]
animalConjectures =
    let kills = pApp "Kills"
        jack = fApp "Jack" []
        tuna = fApp "Tuna" []
        curiosity = fApp "Curiosity" [] in

    map (doTest . withKB animalKB) $
     [ TestFormula
       { formula = kills [jack, tuna]             -- False
       , name = "jack kills tuna"
       , expected =
           [ FirstOrderFormula ((.~.) (((exists "x" ((pApp "Dog" [vt ("x")]) .&. ((pApp "Owns" [fApp ("Jack") [],vt ("x")])))) .&.
                                        (((for_all "x" ((exists "y" ((pApp "Dog" [vt ("y")]) .&. ((pApp "Owns" [vt ("x"),vt ("y")])))) .=>.
                                                          ((pApp "AnimalLover" [vt ("x")])))) .&.
                                          (((for_all "x" ((pApp "AnimalLover" [vt ("x")]) .=>.
                                                            ((for_all "y" ((pApp "Animal" [vt ("y")]) .=>.
                                                                             (((.~.) (pApp "Kills" [vt ("x"),vt ("y")])))))))) .&.
                                            ((((pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]) .|. ((pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []]))) .&.
                                              (((pApp "Cat" [fApp ("Tuna") []]) .&.
                                                ((for_all "x" ((pApp "Cat" [vt ("x")]) .=>.
                                                                 ((pApp "Animal" [vt ("x")])))))))))))))) .=>.
                                       ((pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]))))

           , PrenexNormalForm
             (for_all "x"
              (for_all "y"
               (exists "x'"
                ((((pApp ("Dog") [vt ("x'")]) .&.
                   ((pApp ("Owns") [fApp ("Jack") [],vt ("x'")]))) .&.
                  ((((((.~.) (pApp ("Dog") [vt ("y")])) .|.
                      (((.~.) (pApp ("Owns") [vt ("x"),vt ("y")])))) .|.
                     ((pApp ("AnimalLover") [vt ("x")]))) .&.
                    (((((.~.) (pApp ("AnimalLover") [vt ("x")])) .|.
                       ((((.~.) (pApp ("Animal") [vt ("y")])) .|.
                         (((.~.) (pApp ("Kills") [vt ("x"),vt ("y")])))))) .&.
                      ((((pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []]) .|.
                         ((pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]))) .&.
                        (((pApp ("Cat") [fApp ("Tuna") []]) .&.
                          ((((.~.) (pApp ("Cat") [vt ("x")])) .|.
                            ((pApp ("Animal") [vt ("x")]))))))))))))) .&.
                 (((.~.) (pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])))))))
           , ClauseNormalForm
             (toSS
              [[(pApp ("Animal") [vt ("x")]),
                ((.~.) (pApp ("Cat") [vt ("x")]))],
               [(pApp ("AnimalLover") [vt ("x")]),
                ((.~.) (pApp ("Dog") [vt ("y")])),
                ((.~.) (pApp ("Owns") [vt ("x"),vt ("y")]))],
               [(pApp ("Cat") [fApp ("Tuna") []])],
               [(pApp ("Dog") [fApp (toSkolem "x" 1) []])],
               [(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),
                (pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])],
               [(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x" 1) []])],
               [((.~.) (pApp ("Animal") [vt ("y")])),
                ((.~.) (pApp ("AnimalLover") [vt ("x")])),
                ((.~.) (pApp ("Kills") [vt ("x"),vt ("y")]))],
               [((.~.) (pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []]))]])
           , ChiouKB1
             (Proof
              Invalid
              (Set.fromList
               [makeINF' ([]) ([(pApp ("Cat") [fApp ("Tuna") []])]),
                makeINF' ([]) ([(pApp ("Dog") [fApp (toSkolem "x" 1) []])]),
                makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]),
                makeINF' ([]) ([(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x" 1) []])]),
                makeINF' ([(pApp ("Animal") [vt ("y")]),(pApp ("AnimalLover") [vt ("x")]),(pApp ("Kills") [vt ("x"),vt ("y")])]) ([]),
                makeINF' ([(pApp ("Cat") [vt ("x")])]) ([(pApp ("Animal") [vt ("x")])]),
                makeINF' ([(pApp ("Dog") [vt ("y")]),(pApp ("Owns") [vt ("x"),vt ("y")])]) ([(pApp ("AnimalLover") [vt ("x")])]),
                makeINF' ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]) ([])]))
           ]
       }
     , TestFormula
       { formula = kills [curiosity, tuna]        -- True
       , name = "curiosity kills tuna"
       , expected =
           [ ClauseNormalForm
             (toSS
             [[(pApp "Dog" [fApp (toSkolem "x" 1) []])],
              [(pApp "Owns" [fApp ("Jack") [],fApp (toSkolem "x" 1) []])],
              [((.~.) (pApp "Dog" [vt ("y")])),
               ((.~.) (pApp "Owns" [vt ("x"),vt ("y")])),
               (pApp "AnimalLover" [vt ("x")])],
              [((.~.) (pApp "AnimalLover" [vt ("x")])),
               ((.~.) (pApp "Animal" [vt ("y")])),
               ((.~.) (pApp "Kills" [vt ("x"),vt ("y")]))],
              [(pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]),
               (pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []])],
              [(pApp "Cat" [fApp ("Tuna") []])],
              [((.~.) (pApp "Cat" [vt ("x")])),
               (pApp "Animal" [vt ("x")])],
              [((.~.) (pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]))]])
           , PropLogicSat True
{-
           , SatSolverCNF [ [Neg 1,Neg 2,Neg 3]    -- animallover(x)|animal(y)|kills(x,y)
                          , [Neg 4,Pos 5]          -- ~cat(x)|animal(x)
                          , [Neg 6,Neg 7,Pos 2]    -- ~dog(y)|~owns(x,y)|animallover(x)
                          , [Neg 8]                -- ~kills(curisity,tuna)
                          , [Pos 8,Pos 11]         -- kills(curiosity,tuna)|kills(jack,tuna)
                          , [Pos 9]                -- cat(tuna)
                          , [Pos 10]               -- owns(jack,sk1)
                          , [Pos 12]               -- dog(sk1)
                          ]
-}
           -- I haven't tried to figure out if this is correct, it
           -- probably is because things are working.
           , SatSolverCNF [[Neg 2,Pos 1],[Neg 3,Neg 11,Neg 12],[Neg 4,Neg 5,Pos 3],[Neg 8],[Pos 6],[Pos 7],[Pos 8,Pos 9],[Pos 10]]
           -- It seems like this should be True.
           , SatSolverSat False
           ]
       }
     ]

socratesKB :: forall t formula atom predicate v term.
              (atom ~ AtomOf formula, v ~ VarOf formula, term ~ TermOf atom, predicate ~ PredOf atom,
               Ord formula, IsString t,
               IsQuantified formula,
               HasApply atom,
               IsTerm term) =>
             (t, [TestFormula formula atom v])
socratesKB =
    let x = vt "x"
        socrates x = pApp "Socrates" [x]
        human x = pApp "Human" [x]
        mortal x = pApp "Mortal" [x] in
    ("socrates"
    , [ TestFormula
       { name = "all humans are mortal"
       , formula = for_all "x" (human x .=>. mortal x)
       , expected = [ClauseNormalForm  (toSS [[((.~.) (human x)), mortal x]])] }
     , TestFormula
       { name = "socrates is human"
       , formula = for_all "x" (socrates x .=>. human x)
       , expected = [ClauseNormalForm  (toSS [[(.~.) (socrates x), human x]])] }
     ])

{-
socratesConjectures =
    map (withKB socratesKB)
     [ TestFormula
       { formula = for_all' [V "x"] (socrates x .=>. mortal x)
       , name = "socrates is mortal"
       , expected = [ FirstOrderFormula ((.~.) (((for_all' [V "x"] ((pApp "Human" [vt "x"]) .=>. ((pApp "Mortal" [vt "x"])))) .&.
                                                 ((for_all' [V "x"] ((pApp "Socrates" [vt "x"]) .=>. ((pApp "Human" [vt "x"])))))) .=>.
                                                ((for_all' [V "x"] ((pApp "Socrates" [vt "x"]) .=>. ((pApp "Mortal" [vt "x"])))))))
                    , ClauseNormalForm  [[((.~.) (pApp "Human" [vt "x'"])),(pApp "Mortal" [vt "x'"])],
                                          [((.~.) (pApp "Socrates" [vt "x'"])),(pApp "Human" [vt "x'"])],
                                          [(pApp "Socrates" [fApp (toSkolem "x" 1) [vt "x'",vt "x'"]])],
                                          [((.~.) (pApp "Mortal" [fApp (toSkolem "x" 1) [vt "x'",vt "x'"]]))]]
                    , SatPropLogic True ]
       }
     , TestFormula
       { formula = (.~.) (for_all' [V "x"] (socrates x .=>. mortal x))
       , name = "not (socrates is mortal)"
       , expected = [ SatPropLogic False
                    , FirstOrderFormula ((.~.) (((for_all' [V "x"] ((pApp "Human" [vt "x"]) .=>. ((pApp "Mortal" [vt "x"])))) .&.
                                                 ((for_all' [V "x"] ((pApp "Socrates" [vt "x"]) .=>. ((pApp "Human" [vt "x"])))))) .=>.
                                                (((.~.) (for_all' [V "x"] ((pApp "Socrates" [vt "x"]) .=>. ((pApp "Mortal" [vt "x"]))))))))
                    -- [~human(x) | mortal(x)], [~socrates(Sk1(x,y)) | human(Sk1(x,y))], socrates(Sk1(x,y)), ~mortal(Sk1(x,y))
                    -- ~1 | 2, ~3 | 4, 3, ~5?
                    , ClauseNormalForm [[((.~.) (pApp "Human" [x])), (pApp "Mortal" [x])],
                                         [((.~.) (pApp "Socrates" [fApp (toSkolem "x" 1) [x,y]])), (pApp "Human" [fApp (toSkolem "x" 1) [x,y]])],
                                         [(pApp "Socrates" [fApp (toSkolem "x" 1) [x,y]])], [((.~.) (pApp "Mortal" [fApp (toSkolem "x" 1) [x,y]]))]]
                    , ClauseNormalForm [[((.~.) (pApp "Human" [vt "x'"])), (pApp "Mortal" [vt "x'"])],
                                         [((.~.) (pApp "Socrates" [vt "x'"])), (pApp "Human" [vt "x'"])],
                                         [((.~.) (pApp "Socrates" [vt "x"])), (pApp "Mortal" [vt "x"])]] ]
       }
     ]
-}

chang43KB :: (String, [TestFormula Formula SkAtom V])
chang43KB =
    let e = fApp "e" []
        (x, y, z, u, v, w) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "z" :: SkTerm, vt "u" :: SkTerm, vt "v" :: SkTerm, vt "w" :: SkTerm) in
    ("chang example 4.3"
    , [ TestFormula { name = "closure property"
                    , formula = for_all' ["x", "y"] (exists "z" (pApp "P" [x,y,z]))
                    , expected = [] }
      , TestFormula { name = "associativity property"
                    , formula = for_all' ["x", "y", "z", "u", "v", "w"] (pApp "P" [x, y, u] .&. pApp "P" [y, z, v] .&. pApp "P" [u, z, w] .=>. pApp "P" [x, v, w]) .&.
                                for_all' ["x", "y", "z", "u", "v", "w"] (pApp "P" [x, y, u] .&. pApp "P" [y, z, v] .&. pApp "P" [x, v, w] .=>. pApp "P" [u, z, w])
                    , expected = [] }
      , TestFormula { name = "identity property"
                    , formula = (for_all "x" (pApp "P" [x,e,x])) .&. (for_all "x" (pApp "P" [e,x,x]))
                    , expected = [] }
      , TestFormula { name = "inverse property"
                    , formula = (for_all "x" (pApp "P" [x,fApp "i" [x], e])) .&. (for_all "x" (pApp "P" [fApp "i" [x], x, e]))
                    , expected = [] }
      ])

chang43Conjecture :: Test
chang43Conjecture =
    let e = (fApp "e" [])
        (x, u, v, w) = (vt "x" :: SkTerm, vt "u" :: SkTerm, vt "v" :: SkTerm, vt "w" :: SkTerm) in
    doTest . withKB chang43KB $
    TestFormula { name = "G is commutative"
                , formula = for_all "x" (pApp "P" [x, x, e] .=>. (for_all' ["u", "v", "w"] (pApp "P" [u, v, w] .=>. pApp "P" [v, u, w])))
                , expected =
                    [ FirstOrderFormula
                      ((.~.) (((for_all' ["x","y"] (exists "z" (pApp "P" [vt ("x"),vt ("y"),vt ("z")]))) .&. ((((for_all' ["x","y","z","u","v","w"] ((((pApp "P" [vt ("x"),vt ("y"),vt ("u")]) .&. ((pApp "P" [vt ("y"),vt ("z"),vt ("v")]))) .&. ((pApp "P" [vt ("u"),vt ("z"),vt ("w")]))) .=>. ((pApp "P" [vt ("x"),vt ("v"),vt ("w")])))) .&. ((for_all' ["x","y","z","u","v","w"] ((((pApp "P" [vt ("x"),vt ("y"),vt ("u")]) .&. ((pApp "P" [vt ("y"),vt ("z"),vt ("v")]))) .&. ((pApp "P" [vt ("x"),vt ("v"),vt ("w")]))) .=>. ((pApp "P" [vt ("u"),vt ("z"),vt ("w")])))))) .&. ((((for_all "x" (pApp "P" [vt ("x"),fApp ("e") [],vt ("x")])) .&. ((for_all "x" (pApp "P" [fApp ("e") [],vt ("x"),vt ("x")])))) .&. (((for_all "x" (pApp "P" [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []])) .&. ((for_all "x" (pApp "P" [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []])))))))))) .=>. ((for_all "x" ((pApp "P" [vt ("x"),vt ("x"),fApp ("e") []]) .=>. ((for_all' ["u","v","w"] ((pApp "P" [vt ("u"),vt ("v"),vt ("w")]) .=>. ((pApp "P" [vt ("v"),vt ("u"),vt ("w")]))))))))))
                      -- (∀x ∀y ∃z P(x,y,z)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(u,z,w) | P(x,v,w)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(x,v,w) | P(u,z,w)) &
                      -- (∀x P(x,e,x)) &
                      -- (∀x P(e,x,x)) &
                      -- (∀x P(x,i[x],e)) &
                      -- (∀x P(i[x],x,e)) &
                      -- (∃x P(x,x,e) & (∃u∃v∃w P(u,v,w) & ~P(v,u,w)))
                    , NegationNormalForm
                      (((for_all "x"
                         (for_all "y"
                          (exists "z"
                           (pApp ("P") [vt ("x"),vt ("y"),vt ("z")])))) .&.
                        ((((for_all "x"
                            (for_all "y"
                             (for_all "z"
                              (for_all "u"
                               (for_all "v"
                                (for_all "w"
                                 (((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                                    (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                                   (((.~.) (pApp ("P") [vt ("u"),vt ("z"),vt ("w")])))) .|.
                                  ((pApp ("P") [vt ("x"),vt ("v"),vt ("w")]))))))))) .&.
                           ((for_all "x"
                             (for_all "y"
                              (for_all "z"
                               (for_all "u"
                                (for_all "v"
                                 (for_all "w"
                                  (((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                                     (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                                    (((.~.) (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])))) .|.
                                   ((pApp ("P") [vt ("u"),vt ("z"),vt ("w")]))))))))))) .&.
                          ((((for_all "x" (pApp ("P") [vt ("x"),fApp ("e") [],vt ("x")])) .&.
                             ((for_all "x" (pApp ("P") [fApp ("e") [],vt ("x"),vt ("x")])))) .&.
                            (((for_all "x" (pApp ("P") [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []])) .&.
                              ((for_all "x" (pApp ("P") [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []])))))))))) .&.
                       ((exists "x"
                         ((pApp ("P") [vt ("x"),vt ("x"),fApp ("e") []]) .&.
                          ((exists "u"
                            (exists "v"
                             (exists "w"
                              ((pApp ("P") [vt ("u"),vt ("v"),vt ("w")]) .&.
                               (((.~.) (pApp ("P") [vt ("v"),vt ("u"),vt ("w")]))))))))))))
                    , PrenexNormalForm
                      (for_all "x"
                       (for_all "y"
                        (for_all "z"
                         (for_all "u"
                          (for_all "v"
                           (for_all "w"
                            (exists "z'"
                             (exists "x'"
                              (exists "u'"
                               (exists "v'"
                                (exists "w'"
                                 (((pApp ("P") [vt ("x"),vt ("y"),vt ("z'")]) .&.
                                   ((((((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                                         (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                                        (((.~.) (pApp ("P") [vt ("u"),vt ("z"),vt ("w")])))) .|.
                                       ((pApp ("P") [vt ("x"),vt ("v"),vt ("w")]))) .&.
                                      ((((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                                          (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                                         (((.~.) (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])))) .|.
                                        ((pApp ("P") [vt ("u"),vt ("z"),vt ("w")]))))) .&.
                                     ((((pApp ("P") [vt ("x"),fApp ("e") [],vt ("x")]) .&.
                                        ((pApp ("P") [fApp ("e") [],vt ("x"),vt ("x")]))) .&.
                                       (((pApp ("P") [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []]) .&.
                                         ((pApp ("P") [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []]))))))))) .&.
                                  (((pApp ("P") [vt ("x'"),vt ("x'"),fApp ("e") []]) .&.
                                    (((pApp ("P") [vt ("u'"),vt ("v'"),vt ("w'")]) .&.
                                      (((.~.) (pApp ("P") [vt ("v'"),vt ("u'"),vt ("w'")])))))))))))))))))))
                    , SkolemNormalForm
                      (((pApp ("P") [vt ("x"),vt ("y"),fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]]) .&.
                        ((((((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                              (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                             (((.~.) (pApp ("P") [vt ("u"),vt ("z"),vt ("w")])))) .|.
                            ((pApp ("P") [vt ("x"),vt ("v"),vt ("w")]))) .&.
                           ((((((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])) .|.
                               (((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])))) .|.
                              (((.~.) (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])))) .|.
                             ((pApp ("P") [vt ("u"),vt ("z"),vt ("w")]))))) .&.
                          ((((pApp ("P") [vt ("x"),fApp ("e") [],vt ("x")]) .&.
                             ((pApp ("P") [fApp ("e") [],vt ("x"),vt ("x")]))) .&.
                            (((pApp ("P") [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []]) .&.
                              ((pApp ("P") [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []]))))))))) .&.
                       (((pApp ("P") [fApp (toSkolem "x" 1) [],fApp (toSkolem "x" 1) [],fApp ("e") []]) .&.
                         (((pApp ("P") [fApp (toSkolem "u" 1) [],fApp (toSkolem "v" 1) [],fApp (toSkolem "w" 1) []]) .&.
                           (((.~.) (pApp ("P") [fApp (toSkolem "v" 1) [],fApp (toSkolem "u" 1) [],fApp (toSkolem "w" 1) []]))))))))
                    , SkolemNumbers (Set.fromList [toSkolem "u" 1,toSkolem "v" 1,toSkolem "w" 1,toSkolem "x" 1,toSkolem "z" 1])
                    -- From our algorithm

                    , ClauseNormalForm
                      (toSS
                      [[(pApp ("P") [vt ("x"),vt ("y"),fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]])],
                       [((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])),
                        ((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])),
                        ((.~.) (pApp ("P") [vt ("u"),vt ("z"),vt ("w")])),
                        (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])],
                       [((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])),
                        ((.~.) (pApp ("P") [vt ("y"),vt ("z"),vt ("v")])),
                        ((.~.) (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])),
                        (pApp ("P") [vt ("u"),vt ("z"),vt ("w")])],
                       [(pApp ("P") [vt ("x"),fApp ("e") [],vt ("x")])],
                       [(pApp ("P") [fApp ("e") [],vt ("x"),vt ("x")])],
                       [(pApp ("P") [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []])],
                       [(pApp ("P") [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []])],
                       [(pApp ("P") [fApp (toSkolem "x" 1) [],fApp (toSkolem "x" 1) [],fApp ("e") []])],
                       [(pApp ("P") [fApp (toSkolem "u" 1) [],fApp (toSkolem "v" 1) [],fApp (toSkolem "w" 1) []])],
                       [((.~.) (pApp ("P") [fApp (toSkolem "v" 1) [],fApp (toSkolem "u" 1) [],fApp (toSkolem "w" 1) []]))]])

                    -- From the book
{-
                    , let (a, b, c) =
                              (fApp (toSkolem "x" 1) [vt ("x"),vt ("y"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u"),vt ("v"),vt ("w"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u'"),vt ("v'"),vt ("w'"),vt ("x''"),vt ("x''"),vt ("x''"),vt ("x''")],
                               fApp (toSkolem "x" 1) [vt ("x"),vt ("y"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u"),vt ("v"),vt ("w"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u'"),vt ("v'"),vt ("w'"),vt ("x''"),vt ("x''"),vt ("x''"),vt ("x''")],
                               fApp (toSkolem "x" 1) [vt ("x"),vt ("y"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u"),vt ("v"),vt ("w"),vt ("x'"),vt ("y'"),vt ("z'"),vt ("u'"),vt ("v'"),vt ("w'"),vt ("x''"),vt ("x''"),vt ("x''"),vt ("x''")]) in
                      ClauseNormalForm
                      [[(pApp "P" [vt "x",vt "y",fApp (toSkolem "x" 1) [vt "x",vt "y"]])],
                       [((.~.) (pApp "P" [vt "x",vt "y",vt "u"])),
                        ((.~.) (pApp "P" [vt "y",vt "z",vt "v"])),
                        ((.~.) (pApp "P" [vt "u",vt "z",vt "w"])),
                        (pApp "P" [vt "x",vt "v",vt "w"])],
                       [((.~.) (pApp "P" [vt "x",vt "y",vt "u"])),
                        ((.~.) (pApp "P" [vt "y",vt "z",vt "v"])),
                        ((.~.) (pApp "P" [vt "x",vt "v",vt "w"])),
                        (pApp "P" [vt "u",vt "z",vt "w"])],
                       [(pApp "P" [vt "x",fApp "e" [],vt "x"])],
                       [(pApp "P" [fApp "e" [],vt "x",vt "x"])],
                       [(pApp "P" [vt "x",fApp "i" [vt "x"],fApp "e" []])],
                       [(pApp "P" [fApp "i" [vt "x"],vt "x",fApp "e" []])],
                       [(pApp "P" [vt "x",
                                   vt "x",
                                   fApp "e" []])],
                       [(pApp "P" [a, b, c])],
                       [((.~.) (pApp "P" [b, a, c]))]]
-}
                    ]
                }

{-
% ghci
> :load Test/Data.hs
> :m +Logic.FirstOrder
> :m +Logic.Normal
> let f = (.~.) (conj (map formula (snd chang43KB)) .=>. formula chang43Conjecture)
> putStrLn (runNormal (cnfTrace f))
-}

chang43ConjectureRenamed :: Test
chang43ConjectureRenamed =
    let e = fApp "e" []
        (x, y, z, u, v, w) = (vt "x" :: SkTerm, vt "y" :: SkTerm, vt "z" :: SkTerm, vt "u" :: SkTerm, vt "v" :: SkTerm, vt "w" :: SkTerm)
        (u2, v2, w2, x2, y2, z2, u3, v3, w3, x3, y3, z3, x4, x5, x6, x7, x8) =
            (vt "u'" :: SkTerm, vt "v'" :: SkTerm, vt "w'" :: SkTerm, vt "x'" :: SkTerm, vt "y'" :: SkTerm, vt "z'" :: SkTerm, vt "u3" :: SkTerm, vt "v3" :: SkTerm, vt "w3" :: SkTerm, vt "x3" :: SkTerm, vt "y3" :: SkTerm, vt "z3" :: SkTerm, vt "x4" :: SkTerm, vt "x5" :: SkTerm, vt "x6" :: SkTerm, vt "x7" :: SkTerm, vt "x8" :: SkTerm) in
    doTest $
    TestFormula { name = "chang 43 renamed"
                , formula = (.~.) ((for_all' ["x", "y"] (exists "z" (pApp "P" [x,y,z])) .&.
                                    for_all' ["x'", "y'", "z'", "u", "v", "w"] (pApp "P" [x2, y2, u] .&. pApp "P" [y2, z2, v] .&. pApp "P" [u, z2, w] .=>. pApp "P" [x2, v, w]) .&.
                                    for_all' ["x3", "y3", "z3", "u'", "v'", "w'"] (pApp "P" [x3, y3, u2] .&. pApp "P" [y3, z3, v2] .&. pApp "P" [x3, v2, w2] .=>. pApp "P" [u2, z3, w2]) .&.
                                    for_all "x4" (pApp "P" [x4,e,x4]) .&.
                                    for_all "x5" (pApp "P" [e,x5,x5]) .&.
                                    for_all "x6" (pApp "P" [x6,fApp "i" [x6], e]) .&.
                                    for_all "x7" (pApp "P" [fApp "i" [x7], x7, e])) .=>.
                                   (for_all "x8" (pApp "P" [x8, x8, e] .=>. (for_all' ["u3", "v3", "w3"] (pApp "P" [u3, v3, w3] .=>. pApp "P" [v3, u3, w3])))))
                , expected =
                    [ FirstOrderFormula
                      ((.~.) ((((((((for_all' ["x","y"] (exists "z" (pApp "P" [vt "x",vt "y",vt "z"]))) .&.
                                    ((for_all' ["x'","y'","z'","u","v","w"] ((((pApp "P" [vt "x'",vt "y'",vt "u"]) .&.
                                                                                          ((pApp "P" [vt "y'",vt "z'",vt "v"]))) .&.
                                                                                         ((pApp "P" [vt "u",vt "z'",vt "w"]))) .=>.
                                                                                        ((pApp "P" [vt "x'",vt "v",vt "w"])))))) .&.
                                   ((for_all' ["x3","y3","z3","u'","v'","w'"] ((((pApp "P" [vt "x3",vt "y3",vt "u'"]) .&.
                                                                                            ((pApp "P" [vt "y3",vt "z3",vt "v'"]))) .&.
                                                                                           ((pApp "P" [vt "x3",vt "v'",vt "w'"]))) .=>.
                                                                                          ((pApp "P" [vt "u'",vt "z3",vt "w'"])))))) .&.
                                  ((for_all "x4" (pApp "P" [vt "x4",fApp "e" [],vt "x4"])))) .&.
                                 ((for_all "x5" (pApp "P" [fApp "e" [],vt "x5",vt "x5"])))) .&.
                                ((for_all "x6" (pApp "P" [vt "x6",fApp "i" [vt "x6"],fApp "e" []])))) .&.
                               ((for_all "x7" (pApp "P" [fApp "i" [vt "x7"],vt "x7",fApp "e" []])))) .=>.
                              ((for_all "x8" ((pApp "P" [vt "x8",vt "x8",fApp "e" []]) .=>.
                                                  ((for_all' ["u3","v3","w3"] ((pApp "P" [vt "u3",vt "v3",vt "w3"]) .=>.
                                                                                    ((pApp "P" [vt "v3",vt "u3",vt "w3"]))))))))))
                    , let a = fApp (toSkolem "u3" 1) []
                          b = fApp (toSkolem "v3" 1) []
                          c = fApp (toSkolem "w3" 1) [] in
                      ClauseNormalForm
                      (toSS
                      [[(pApp ("P") [vt ("x"),vt ("y"),fApp (toSkolem "z" 1) [vt ("x"),vt ("y")]])],
                       [((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])),
                        ((.~.) (pApp ("P") [vt ("y"),vt ("z'"),vt ("v")])),
                        ((.~.) (pApp ("P") [vt ("u"),vt ("z'"),vt ("w")])),
                        (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])],
                       [((.~.) (pApp ("P") [vt ("x"),vt ("y"),vt ("u")])),
                        ((.~.) (pApp ("P") [vt ("y"),vt ("z'"),vt ("v")])),
                        ((.~.) (pApp ("P") [vt ("x"),vt ("v"),vt ("w")])),
                        (pApp ("P") [vt ("u"),vt ("z'"),vt ("w")])],
                       [(pApp ("P") [vt ("x"),fApp ("e") [],vt ("x")])],
                       [(pApp ("P") [fApp ("e") [],vt ("x"),vt ("x")])],
                       [(pApp ("P") [vt ("x"),fApp ("i") [vt ("x")],fApp ("e") []])],
                       [(pApp ("P") [fApp ("i") [vt ("x")],vt ("x"),fApp ("e") []])],
                       [(pApp ("P") [fApp (toSkolem "x8" 1) [],fApp (toSkolem "x8" 1) [],fApp ("e") []])],
                       [(pApp ("P") [a,b,c])],
                       [((.~.) (pApp ("P") [b,a,c]))]])
                    ]
                }

withKB :: forall formula atom term v.
          (formula ~ Formula, atom ~ SkAtom, v ~ V,
           term ~ TermOf atom,
           IsQuantified formula, HasEquate atom, IsTerm term) =>
          (String, [TestFormula formula atom v]) -> TestFormula formula atom v -> TestFormula formula atom v
withKB (kbName, knowledge) conjecture =
    conjecture { name = name conjecture ++ " with " ++ kbName ++ " knowledge base"
               -- Here we say that the conjunction of the knowledge
               -- base formula implies the conjecture.  We prove the
               -- theorem by showing that the negation is
               -- unsatisfiable.
               , formula = (.~.) (conj (map formula knowledge) .=>. formula conjecture)}
    where
      conj [] = error "conj []"
      conj [x] = x
      conj (x:xs) = x .&. conj xs

kbKnowledge :: forall formula atom term v.
               (formula ~ Formula, atom ~ SkAtom, v ~ V, term ~ TermOf atom,
                IsQuantified formula, HasEquate atom, IsTerm term) =>
               (String, [TestFormula formula atom v]) -> (String, [formula])
kbKnowledge kb = (fst (kb :: (String, [TestFormula formula atom v])), map formula (snd kb))

proofs :: [TestProof Formula SkAtom SkTerm V]
proofs =
    let -- dog = pApp "Dog" :: [term] -> formula
        -- cat = pApp "Cat" :: [term] -> formula
        -- owns = pApp "Owns" :: [term] -> formula
        kills = pApp "Kills"
        -- animal = pApp "Animal" :: [term] -> formula
        -- animalLover = pApp "AnimalLover" :: [term] -> formula
        socrates = pApp "Socrates"
        -- human = pApp "Human" :: [term] -> formula
        mortal = pApp "Mortal"

        jack = fApp "Jack" []
        tuna = fApp "Tuna" []
        curiosity = fApp "Curiosity" [] in

    [ TestProof
      { proofName = "prove jack kills tuna"
      , proofKnowledge = kbKnowledge animalKB
      , conjecture = kills [jack, tuna]
      , proofExpected =
          [ ChiouKB (Set.fromList
                     [WithId {wiItem = INF (Set.fromList []) (Set.fromList [(pApp "Dog" [fApp (toSkolem "x" 1) []])]), wiIdent = 1},
                      WithId {wiItem = INF (Set.fromList []) (Set.fromList [(pApp "Owns" [fApp "Jack" [],fApp (toSkolem "x" 1) []])]), wiIdent = 1},
                      WithId {wiItem = INF (Set.fromList [(pApp "Dog" [vt "y"]),(pApp "Owns" [vt "x",vt "y"])]) (Set.fromList [(pApp "AnimalLover" [vt "x"])]), wiIdent = 2},
                      WithId {wiItem = INF (Set.fromList [(pApp "Animal" [vt "y"]),(pApp "AnimalLover" [vt "x"]),(pApp "Kills" [vt "x",vt "y"])]) (Set.fromList []), wiIdent = 3},
                      WithId {wiItem = INF (Set.fromList []) (Set.fromList [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]),(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])]), wiIdent = 4},
                      WithId {wiItem = INF (Set.fromList []) (Set.fromList [(pApp "Cat" [fApp "Tuna" []])]), wiIdent = 5},
                      WithId {wiItem = INF (Set.fromList [(pApp "Cat" [vt "x"])]) (Set.fromList [(pApp "Animal" [vt "x"])]), wiIdent = 6}])
          , ChiouResult (False,
                         (Set.fromList
                          [(inf' [(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])] [],Map.fromList []),
                           (inf' [] [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []])],Map.fromList []),
                           (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "AnimalLover" [fApp "Curiosity" []])] [],Map.fromList []),
                           (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Dog" [vt "y"]),(pApp "Owns" [fApp "Curiosity" [],vt "y"])] [],Map.fromList []),
                           (inf' [(pApp "AnimalLover" [fApp "Curiosity" []]),(pApp "Cat" [fApp "Tuna" []])] [],Map.fromList []),
                           (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem "x" 1) []])] [],Map.fromList []),
                           (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Dog" [vt "y"]),(pApp "Owns" [fApp "Curiosity" [],vt "y"])] [],Map.fromList []),
                           (inf' [(pApp "AnimalLover" [fApp "Curiosity" []])] [],Map.fromList []),
                           (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem "x" 1) []])] [],Map.fromList []),
                           (inf' [(pApp "Dog" [vt "y"]),(pApp "Owns" [fApp "Curiosity" [],vt "y"])] [],Map.fromList []),
                           (inf' [(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem "x" 1) []])] [],Map.fromList [])]))
          ]
      }
    , TestProof
      { proofName = "prove curiosity kills tuna"
      , proofKnowledge = kbKnowledge animalKB
      , conjecture = kills [curiosity, tuna]
      , proofExpected =
          [ ChiouKB (Set.fromList
                     [WithId {wiItem = inf' []                                 [(pApp "Dog" [fApp (toSkolem "x" 1) []])],                 wiIdent = 1},
                      WithId {wiItem = inf' []                                 [(pApp "Owns" [fApp "Jack" [],fApp (toSkolem "x" 1) []])], wiIdent = 1},
                      WithId {wiItem = inf' [(pApp "Dog" [vt "y"]),
                                             (pApp "Owns" [vt "x",vt "y"])]  [(pApp "AnimalLover" [vt "x"])],                      wiIdent = 2},
                      WithId {wiItem = inf' [(pApp "Animal" [vt "y"]),
                                             (pApp "AnimalLover" [vt "x"]),
                                             (pApp "Kills" [vt "x",vt "y"])] [], wiIdent = 3},
                      WithId {wiItem = inf' []                                 [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]),
                                                                                (pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])],      wiIdent = 4},
                      WithId {wiItem = inf' []                                 [(pApp "Cat" [fApp "Tuna" []])],                       wiIdent = 5},
                      WithId {wiItem = inf' [(pApp "Cat" [vt "x"])]           [(pApp "Animal" [vt "x"])],                           wiIdent = 6}])
          , ChiouResult (True,
                         Set.fromList
                         [(makeINF' ([]) ([]),Map.fromList []),
                          (makeINF' ([]) ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]),Map.fromList []),
                          (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [fApp (toSkolem "x" 1) []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x" 1) []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [fApp (toSkolem "x" 1) []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x" 1) []])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Dog") [vt ("y")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),Map.fromList []),
                          (makeINF' ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]) ([]),Map.fromList [])])
          ]
      }
{-
  -- Seems not to terminate
    , let (x, u, v, w, e) = (vt "x", vt "u", vt "v", vt "w", vt "e") in
      TestProof
      { proofName = "chang example 4.3"
      , proofKnowledge = (fst chang43KB, map (convertFOF id id id . formula) (snd chang43KB))
      , conjecture = for_all' ["x"] (pApp "P" [x, x, e] .=>. (for_all' ["u", "v", "w"] (pApp "P" [u, v, w] .=>. pApp "P" [v, u, w])))
      , proofExpected =
          [ChiouResult (True, [])]
      }
-}
    , let x = vt "x" in
      TestProof
      { proofName = "socrates is mortal"
      , proofKnowledge = kbKnowledge (socratesKB)
      , conjecture = for_all "x" (socrates [x] .=>. mortal [x])
      , proofExpected =
         [ ChiouKB (Set.fromList
                    [WithId {wiItem = inf' [(pApp "Human" [vt "x"])] [(pApp "Mortal" [vt "x"])], wiIdent = 1},
                     WithId {wiItem = inf' [(pApp "Socrates" [vt "x"])] [(pApp "Human" [vt "x"])], wiIdent = 2}])
         , ChiouResult (True,
                        Set.fromList
                        [(makeINF' ([]) ([]),Map.fromList []),
                         (makeINF' ([]) ([(pApp ("Human") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                         (makeINF' ([]) ([(pApp ("Mortal") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                         (makeINF' ([]) ([(pApp ("Socrates") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                         (makeINF' ([(pApp ("Mortal") [fApp (toSkolem "x" 1) []])]) ([]),Map.fromList [])])]
      }
    , let x = vt "x" in
      TestProof
      { proofName = "socrates is not mortal"
      , proofKnowledge = kbKnowledge (socratesKB)
      , conjecture = (.~.) (for_all "x" (socrates [x] .=>. mortal [x]))
      , proofExpected =
         [ ChiouKB (Set.fromList
                    [WithId {wiItem = inf' [(pApp "Human" [vt "x"])] [(pApp "Mortal" [vt "x"])], wiIdent = 1},
                     WithId {wiItem = inf' [(pApp "Socrates" [vt "x"])] [(pApp "Human" [vt "x"])], wiIdent = 2}])
         , ChiouResult (False
                       ,(Set.fromList [(inf' [(pApp "Socrates" [vt "x"])] [(pApp "Mortal" [vt "x"])],Map.fromList [("x",vt "x")])]))]
      }
    , let x = vt "x" in
      TestProof
      { proofName = "socrates exists and is not mortal"
      , proofKnowledge = kbKnowledge (socratesKB)
      , conjecture = (.~.) (exists "x" (socrates [x]) .&. for_all "x" (socrates [x] .=>. mortal [x]))
      , proofExpected =
         [ ChiouKB (Set.fromList
                    [WithId {wiItem = inf' [(pApp "Human" [vt "x"])] [(pApp "Mortal" [vt "x"])], wiIdent = 1},
                     WithId {wiItem = inf' [(pApp "Socrates" [vt "x"])] [(pApp "Human" [vt "x"])], wiIdent = 2}])
         , ChiouResult (False,
                        Set.fromList [(makeINF' ([]) ([(pApp ("Human") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                                    (makeINF' ([]) ([(pApp ("Mortal") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                                    (makeINF' ([]) ([(pApp ("Socrates") [fApp (toSkolem "x" 1) []])]),Map.fromList []),
                                    (makeINF' ([(pApp ("Socrates") [vt ("x")])]) ([(pApp ("Mortal") [vt ("x")])]),Map.fromList [("x",vt ("x"))])])
         ]
      }
    ]

inf' :: (IsLiteral lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
inf' = makeINF'

toLL :: Set (Set a) -> [[a]]
toLL = map Set.toList . Set.toList
toSS :: Ord a => [[a]] -> Set (Set a)
toSS = Set.fromList . map Set.fromList
