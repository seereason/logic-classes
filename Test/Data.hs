{-# LANGUAGE DeriveDataTypeable, OverloadedStrings  #-}
{-# OPTIONS -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Test.Data
    ( formulas
    , proofs
    , animalKB
    , animalConjectures
    , chang43KB
    , chang43Conjecture
    , chang43ConjectureRenamed
    ) where

import qualified Data.Set as S
import qualified Logic.Chiou.FirstOrderLogic as C
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..))
import Logic.FirstOrder (FirstOrderLogic(..), Term(..), Skolem(toSkolem), convertFOF)
import Logic.Logic (Logic(..), Boolean(..))
import Test.Types

formulas :: [TestFormula]
formulas =
    let n = (.~.) :: Logic formula => formula -> formula
        p = pApp (Pr "p") :: [ATerm] -> Formula
        q = pApp (Pr "q") :: [ATerm] -> Formula
        r = pApp (Pr "r") :: [ATerm] -> Formula
        s = pApp (Pr "s") :: [ATerm] -> Formula
        t = pApp (Pr "t") :: [ATerm] -> Formula
        p0 = p []
        q0 = q []
        r0 = r []
        s0 = s []
        t0 = t []
        (x, y, z, u, v, w) = (var "x", var "y", var "z", var "u", var "v", var "w") in
    [ 
      TestFormula
      { formula = p0 .|. q0 .&. r0 .|. n s0 .&. n t0
      , name = "operator precedence"
      , expected = [ FirstOrderFormula ((p0 .|. q0) .&. (r0 .|. (n s0)) .&. (n t0)) ] }
    , TestFormula
      { formula = pApp (fromBool True) []
      , name = "True"
      , expected = [ClausalNormalForm  []] }
    , TestFormula
      { formula = pApp (fromBool False) []
      , name = "False"
      , expected = [ClausalNormalForm  [[]]] }
    , TestFormula
      { formula = pApp (Pr "p") []
      , name = "p"
      , expected = [ClausalNormalForm  [[pApp (Pr "p") []]]] }
    , TestFormula
      { formula = pApp (Pr "p") [] .&. ((.~.) (pApp (Pr "p") []))
      , name = "p&~p"
      , expected = [ClausalNormalForm  [[(pApp (Pr "p") [])],[((.~.) (pApp (Pr "p") []))]]] }
    , TestFormula
      { formula = pApp (Pr "p") [var "x"]
      , name = "p[x]"
      , expected = [ClausalNormalForm  [[pApp (Pr "p") [x]]]] }
    , let f = pApp "f"
          q = pApp "q" in
      TestFormula
      { name = "iff"
      , formula = for_all ["x"] (for_all ["y"] (q [x, y] .<=>. for_all ["z"] (f [z, x] .<=>. f [z, y])))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp (Pr "q") [var (V "x"),var (V "y")])),
                      ((.~.) (pApp (Pr "f") [var (V "z"),var (V "x")])),
                      (pApp (Pr "f") [var (V "z"),var (V "y")])],
                     [((.~.) (pApp (Pr "q") [var (V "x"),var (V "y")])),
                      ((.~.) (pApp (Pr "f") [var (V "z"),var (V "y")])),
                      (pApp (Pr "f") [var (V "z"),var (V "x")])],
                     [(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")]),
                      (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")]),
                      (pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")])),
                      (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")]),
                      (pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")]),
                      ((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")])),
                      (pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "y")])),
                      ((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "y"),var (V "z")],var (V "x")])),
                      (pApp (Pr "q") [var (V "x"),var (V "y")])]]]
      }
    , TestFormula
      { name = "move quantifiers out"
      , formula = (for_all ["x"] (pApp "p" [x]) .&. (pApp "q" [x]))
      , expected = [PrenexNormalForm (for_all ["x2"] ((pApp ("p") [var ("x2")]) .&. ((pApp ("q") [var ("x")]))))]
      }
    , TestFormula
      { name = "skolemize1"
      , formula = (exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w]))))))
      , expected = [SkolemNormalForm (for_all [V "y",V "z"] (for_all [V "v"] (pApp "P" [fApp (toSkolem 1) [], y, z, fApp ((toSkolem 2)) [y, z], v, fApp (toSkolem 3) [y, z, v]])))]
      }
    , TestFormula
      { name = "skolemize2"
      , formula = exists ["x"] (for_all ["y"] (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [],y]))]
      }
    , TestFormula
      { name = "skolemize3"
      , formula = for_all ["y"] (exists ["x"] (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (for_all [V "y"] (pApp ("loves") [fApp (toSkolem 1) [y],y]))]
      }
    , TestFormula
      { formula = exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp (Pr "P") [x, y, z, u, v, w])))))
      , name = "chang example 4.1"
      , expected = [ SkolemNormalForm (for_all ["y","z"] (for_all ["v"] (pApp (Pr "P") [fApp (Skolem 1) [], y, z, fApp (Skolem 2) [y, z], v, fApp (Skolem 3) [y, z, v]]))) ] }
    , TestFormula
      { name = "chang example 4.2"
      -- ∀x ∃y∃z ~P(x,y) & Q(x,z) | R(x,y,z)
      , formula = for_all ["x"] (exists ["y", "z"] (((((.~.) (pApp "P" [x, y])) .&. pApp "Q" [x, z]) .|. pApp "R" [x, y, z])))
      -- ∀x ~P(x,Sk1[x]) | R(x,Sk1[x],Sk2[x]) & Q(x,Sk2[x]) | R(x,Sk1[x],Sk2[x])
      , expected = [ SkolemNormalForm (for_all ["x"] ((((.~.) (pApp "P" [x, fApp (Skolem 1) [x]])) .|.
                                                       (pApp "R" [x, fApp (Skolem 1) [x], fApp (Skolem 2) [x]])) .&.
                                                      ((pApp "Q" [x, fApp (Skolem 2) [x]]) .|.
                                                       (pApp "R" [x, fApp (Skolem 1) [x], fApp (Skolem 2) [x]])))) ]
      }
    , TestFormula
      { formula = n p0 .|. q0 .&. p0 .|. r0 .&. n q0 .&. n r0
      , name = "chang 7.2.1a - unsat"
      , expected = [ SatPropLogic False ] }
    , TestFormula
      { formula = p0 .|. q0 .|. r0 .&. n p0 .&. n q0 .&. n r0 .|. s0 .&. n s0
      , name = "chang 7.2.1b - unsat"
      , expected = [SatPropLogic False] }
    , TestFormula
      { formula = p0 .|. q0 .&. q0 .|. r0 .&. r0 .|. s0 .&. n r0 .|. n p0 .&. n s0 .|. n q0 .&. n q0 .|. n r0
      , name = "chang 7.2.1c - unsat"
      , expected = [SatPropLogic False] }
    , TestFormula
      { name = "distribute bug test"
      , formula = ((((.~.) (pApp "q" [var "x",var "y"])) .|.
                    ((((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])) .|.
                      (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .&.
                     (((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                      (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])))) .&.
                   ((((pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]) .&.
                      ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"]))) .|. 
                     ((pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"]) .&.
                      ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])))) .|.
                    (pApp "q" [var "x",var "y"])) {- :: Sentence V Pr AtomicFunction -})
      , expected = [DisjunctiveNormalForm
                    (((((.~.) (pApp (Pr "q") [var "x",var "y"])) .|.
                       (((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])) .|.
                        (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"]))) .&.
                      (((.~.) (pApp (Pr "q") [var "x",var "y"])) .|.
                       (((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])))) .&. 
                     (((((pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]) .|.
                         (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp (Pr "q") [var "x",var "y"])) .&.
                       ((((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                         (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp (Pr "q") [var "x",var "y"]))) .&.
                      ((((pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]) .|.
                         ((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]))) .|.
                        (pApp (Pr "q") [var "x",var "y"])) .&.
                       ((((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                         ((.~.) (pApp (Pr "f") [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]))) .|.
                        (pApp (Pr "q") [var "x",var "y"])))))]
      }
    , let (x, y) = (var "x", var "y")
          (x', y') = (var "x", var "y") in
      TestFormula
      { name = "convert to Chiou 1"
      , formula = exists ["x"] (x .=. y)
      , expected = [ConvertToChiou (exists ["x"] (x' .=. y'))]
      }
    , let s :: [ATerm] -> Formula
          s = pApp "s"
          s' :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
          s' = pApp "s"
          x' :: C.Term V AtomicFunction
          x' = var "x"
          y' :: C.Term V AtomicFunction
          y' = var "y" in
      TestFormula
      { name = "convert to Chiou 2"
      , formula = s [fApp ("a") [x, y]]
      , expected = [ConvertToChiou (s' [fApp "a" [x', y']])]
      }
    , let s :: [ATerm] -> Formula
          s = pApp "s"
          h :: [ATerm] -> Formula
          h = pApp "h"
          m :: [ATerm] -> Formula
          m = pApp "m"
          s' :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
          s' = pApp "s"
          h' :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
          h' = pApp "h"
          m' :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
          m' = pApp "m"
          x' :: C.Term V AtomicFunction
          x' = var "x" in
      TestFormula
      { name = "convert to Chiou 3"
      , formula = for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
      , expected = [ConvertToChiou (for_all ["x"] (((s' [x'] .=>. h' [x']) .&. (h' [x'] .=>. m' [x'])) .=>. (s' [x'] .=>. m' [x'])))]
      }
    , let taller a b = pApp "taller" [a, b]
          wise a = pApp "wise" [a] in
      TestFormula
      { name = "cnf test 1"
      , formula = for_all ["y"] (for_all ["x"] (taller y x .|. wise x) .=>. wise y)
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp (Pr "taller") [var (V "y"),fApp (Skolem 1) [var (V "y")]])),(pApp (Pr "wise") [var (V "y")])],
                     [((.~.) (pApp (Pr "wise") [fApp (Skolem 1) [var (V "y")]])),(pApp (Pr "wise") [var (V "y")])]]]
      }
    , TestFormula
      { name = "cnf test 2"
      , formula = ((.~.) (exists ["x"] (pApp "s" [x] .&. pApp "q" [x])))
      , expected = [ClausalNormalForm [[((.~.) (pApp (Pr "s") [var (V "x")])),((.~.) (pApp (Pr "q") [var (V "x")]))]]]
      }
    , TestFormula
      { name = "cnf test 3"
      , formula = (for_all ["x"] (p [x] .=>. (q [x] .|. r [x])))
      , expected = [ClausalNormalForm [[((.~.) (pApp (Pr "p") [var (V "x")])),(pApp (Pr "q") [var (V "x")]),(pApp (Pr "r") [var (V "x")])]]]
      }
    , TestFormula
      { name = "cnf test 4"
      , formula = ((.~.) (exists ["x"] (p [x] .=>. exists ["y"] (q [y]))))
      , expected = [ClausalNormalForm [[(pApp (Pr "p") [var (V "x")])],[((.~.) (pApp (Pr "q") [var (V "y")]))]]]
      }
    , TestFormula
      { name = "cnf test 5"
      , formula = (for_all ["x"] (q [x] .|. r [x] .=>. s [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp (Pr "q") [var (V "x")])),(pApp (Pr "s") [var (V "x")])],[((.~.) (pApp (Pr "r") [var (V "x")])),(pApp (Pr "s") [var (V "x")])]]]
      }
    , TestFormula
      { name = "cnf test 6"
      , formula = (exists ["x"] (p0 .=>. pApp "f" [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp (Pr "p") [])),(pApp (Pr "f") [fApp (Skolem 1) []])]]]
      }
    , TestFormula
      { name = "cnf test 7"
      , formula = (exists ["x"] (p0 .<=>. pApp "f" [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp (Pr "p") [])),(pApp (Pr "f") [fApp (Skolem 1) []])],[((.~.) (pApp (Pr "f") [fApp (Skolem 1) []])),(pApp (Pr "p") [])]]]
      }
    , TestFormula
      { name = "cnf test 8"
      , formula = (for_all ["z"] (exists ["y"] (for_all ["x"] (pApp "f" [x, y] .<=>. (pApp "f" [x, z] .&. ((.~.) (pApp "f" [x, x])))))))
      , expected = [ClausalNormalForm 
                    [[((.~.) (pApp (Pr "f") [var (V "x"),fApp (Skolem 1) [var (V "z")]])),(pApp (Pr "f") [var (V "x"),var (V "z")])],
                     [((.~.) (pApp (Pr "f") [var (V "x"),fApp (Skolem 1) [var (V "z")]])),((.~.) (pApp (Pr "f") [var (V "x"),var (V "x")]))],
                     [((.~.) (pApp (Pr "f") [var (V "x"),var (V "z")])),(pApp (Pr "f") [var (V "x"),var (V "x")]),(pApp (Pr "f") [var (V "x"),fApp (Skolem 1) [var (V "z")]])]]]
      }
    , TestFormula
      { name = "cnf test 9"
      , formula = (for_all ["x"] (for_all ["x"] (for_all ["y"] (q [x, y] .<=>. for_all [(V "z")] (pApp "f" [z, x] .<=>. pApp "f" [z, y])))))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp (Pr "q") [var (V "x"),var (V "y")])),((.~.) (pApp (Pr "f") [var (V "z"),var (V "x")])),(pApp (Pr "f") [var (V "z"),var (V "y")])],
                     [((.~.) (pApp (Pr "q") [var (V "x"),var (V "y")])),((.~.) (pApp (Pr "f") [var (V "z"),var (V "y")])),(pApp (Pr "f") [var (V "z"),var (V "x")])],
                     [(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "x")]),(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "y")]),(pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "y")])),(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "y")]),(pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [(pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "x")]),((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "x")])),(pApp (Pr "q") [var (V "x"),var (V "y")])],
                     [((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "y")])),((.~.) (pApp (Pr "f") [fApp (Skolem 1) [var (V "x"),var (V "x"),var (V "y"),var (V "z")],var (V "x")])),(pApp (Pr "q") [var (V "x"),var (V "y")])]]]
      }
    , TestFormula
      { name = "cnf test 10"
      , formula = (for_all ["x"] (exists ["y"] ((p [x, y] .<=. for_all ["x"] (exists ["z"] (q [y, x, z]) .=>. r [y])))))
      , expected = [ClausalNormalForm
                    [[(pApp (Pr "q") [fApp (Skolem 1) [var (V "x")],fApp (Skolem 2) [var (V "x")],fApp (Skolem 3) [var (V "x")]]),(pApp (Pr "p") [var (V "x"),fApp (Skolem 1) [var (V "x")]])],
                     [((.~.) (pApp (Pr "r") [fApp (Skolem 1) [var (V "x")]])),(pApp (Pr "p") [var (V "x"),fApp (Skolem 1) [var (V "x")]])]]]
      }
    , TestFormula
      { name = "cnf test 11"
      , formula = (for_all ["x"] (for_all ["z"] (p [x, z] .=>. exists ["y"] ((.~.) (q [x, y] .|. ((.~.) (r [y, z])))))))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp (Pr "p") [var (V "x"),var (V "z")])),((.~.) (pApp (Pr "q") [var (V "x"),fApp (Skolem 1) [var (V "x"),var (V "z")]]))],
                     [((.~.) (pApp (Pr "p") [var (V "x"),var (V "z")])),(pApp (Pr "r") [fApp (Skolem 1) [var (V "x"),var (V "z")],var (V "z")])]]]
      }
    , TestFormula
      { name = "cnf test 12"
      , formula = ((p0 .=>. q0) .=>. (((.~.) r0) .=>. (s0 .&. t0)))
      , expected = [ClausalNormalForm
                    [[(pApp (Pr "p") []),(pApp (Pr "r") []),(pApp (Pr "s") [])],
                     [((.~.) (pApp (Pr "q") [])),(pApp (Pr "r") []),(pApp (Pr "s") [])],
                     [(pApp (Pr "p") []),(pApp (Pr "r") []),(pApp (Pr "t") [])],
                     [((.~.) (pApp (Pr "q") [])),(pApp (Pr "r") []),(pApp (Pr "t") [])]]]
      }
    ]

animalKB :: (String, [TestFormula])
animalKB =
    let x = var "x"
        y = var "y"
        dog = pApp "Dog" :: [ATerm] -> Formula
        cat = pApp "Cat" :: [ATerm] -> Formula
        owns = pApp "Owns" :: [ATerm] -> Formula
        kills = pApp "Kills" :: [ATerm] -> Formula
        animal = pApp "Animal" :: [ATerm] -> Formula
        animalLover = pApp "AnimalLover" :: [ATerm] -> Formula
        jack = fApp "Jack" [] :: ATerm
        tuna = fApp "Tuna" [] :: ATerm
        curiosity = fApp "Curiosity" [] :: ATerm in
    ("animal"
    , [ TestFormula
       { formula = exists [V "x"] (dog [x] .&. owns [jack, x]) -- [[Pos 1],[Pos 2]]
       , name = "jack owns a dog"
       , expected = [ClausalNormalForm  [[(pApp (Pr "Dog") [fApp (Skolem 1) []])],[(pApp (Pr "Owns") [fApp (Fn "Jack") [],fApp (Skolem 1) []])]]]
       -- owns(jack,sK0)
       -- dog (SK0)
                   }
     , TestFormula
       { formula = for_all [V "x"] (((exists ["y"] (dog [y])) .&. (owns [x, y])) .=>. (animalLover [x])) -- [[Neg 1,Neg 2,Pos 3]]
       , name = "dog owners are animal lovers"
       , expected = [ PrenexNormalForm (for_all [V "x"] (for_all [V "y2"] ((((.~.) (pApp (Pr "Dog") [var (V "y2")])) .|.
                                                                            (((.~.) (pApp (Pr "Owns") [var (V "x"),var (V "y")])))) .|.
                                                                           ((pApp (Pr "AnimalLover") [var (V "x")])))))
                    , ClausalNormalForm [[((.~.) (pApp (Pr "Dog") [var (V "y2")])),((.~.) (pApp (Pr "Owns") [var (V "x"),var (V "y")])),(pApp (Pr "AnimalLover") [var (V "x")])]] ]
       -- animalLover(X0) | ~owns(X0,sK1(X0)) | ~dog(sK1(X0))
       }
     , TestFormula
       { formula = for_all [V "x"] ((animalLover [x]) .=>. (for_all [V "y"] ((animal [y]) .=>. ((.~.) (kills [x, y]))))) -- [[Neg 3,Neg 4,Neg 5]]
       , name = "animal lovers don't kill animals"
       , expected = [ClausalNormalForm  [[((.~.) (pApp (Pr "AnimalLover") [var (V "x")])),((.~.) (pApp (Pr "Animal") [var (V "y")])),((.~.) (pApp (Pr "Kills") [var (V "x"),var (V "y")]))]]]
       -- ~kills(X0,X2) | ~animal(X2) | ~animalLover(sK2(X0))
       }
     , TestFormula
       { formula = (kills [jack, tuna]) .|. (kills [curiosity, tuna]) -- [[Pos 5,Pos 5]]
       , name = "Either jack or curiosity kills tuna"
       , expected = [ClausalNormalForm  [[(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []]),(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])]]]
       -- kills(curiosity,tuna) | kills(jack,tuna)
       }
     , TestFormula
       { formula = cat [tuna] -- [[Pos 6]]
       , name = "tuna is a cat"
       , expected = [ClausalNormalForm  [[(pApp (Pr "Cat") [fApp (Fn "Tuna") []])]]]
       -- cat(tuna)
       }
     , TestFormula
       { formula = for_all [V "x"] ((cat [x]) .=>. (animal [x])) -- [[Neg 6,Pos 4]]
       , name = "a cat is an animal"
       , expected = [ClausalNormalForm  [[((.~.) (pApp (Pr "Cat") [var (V "x")])),(pApp (Pr "Animal") [var (V "x")])]]]
       -- animal(X0) | ~cat(X0)
       }
     ])

animalConjectures =
    let kills = pApp "Kills" :: [ATerm] -> Formula
        jack = fApp "Jack" [] :: ATerm
        tuna = fApp "Tuna" [] :: ATerm
        curiosity = fApp "Curiosity" [] :: ATerm in

    map (withKB animalKB) $
     [ TestFormula
       { formula = (.~.) (kills [jack, tuna]) -- [[Neg 5]]            -- Inconsistant
       , name = "not (jack kills tuna)"
       , expected =
           [ ClausalNormalForm  [[(pApp (Pr "Dog") [fApp (Skolem 1) []])],
                                 [(pApp (Pr "Owns") [fApp (Fn "Jack") [],fApp (Skolem 1) []])],
                                 [((.~.) (pApp (Pr "Dog") [var (V "y2")])),((.~.) (pApp (Pr "Owns") [var (V "x2"),var (V "y")])),(pApp (Pr "AnimalLover") [var (V "x2")])],
                                 [((.~.) (pApp (Pr "AnimalLover") [var (V "x2")])),((.~.) (pApp (Pr "Animal") [var (V "y3")])),((.~.) (pApp (Pr "Kills") [var (V "x2"),var (V "y3")]))],
                                 [(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []]),(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])],
                                 [(pApp (Pr "Cat") [fApp (Fn "Tuna") []])],
                                 [((.~.) (pApp (Pr "Cat") [var (V "x2")])),(pApp (Pr "Animal") [var (V "x2")])],
                                 [(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []])]]
           , SatPropLogic True ]
       -- negated_conjecture: ~kills(jack,tuna)
       }
     , TestFormula
       { formula = (.~.) (kills [curiosity, tuna])        -- Theorem
       , name = "not (curiosity kills tuna)"
       , expected =
           [ ClausalNormalForm  [[(pApp (Pr "Dog") [fApp (Skolem 1) []])],
                                 [(pApp (Pr "Owns") [fApp (Fn "Jack") [],fApp (Skolem 1) []])],
                                 [((.~.) (pApp (Pr "Dog") [var (V "y2")])),((.~.) (pApp (Pr "Owns") [var (V "x2"),var (V "y")])),(pApp (Pr "AnimalLover") [var (V "x2")])],
                                 [((.~.) (pApp (Pr "AnimalLover") [var (V "x2")])),((.~.) (pApp (Pr "Animal") [var (V "y3")])),((.~.) (pApp (Pr "Kills") [var (V "x2"),var (V "y3")]))],
                                 [(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []]),(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])],
                                 [(pApp (Pr "Cat") [fApp (Fn "Tuna") []])],
                                 [((.~.) (pApp (Pr "Cat") [var (V "x2")])),(pApp (Pr "Animal") [var (V "x2")])],
                                 [(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])]]
           , SatPropLogic False ]
       -- negated_conjecture: ~kills(curiosity,tuna)
       }
     ]

socratesKB =
    let x = var "x"
        socrates x = pApp (Pr "Socrates") [x]
        human x = pApp "Human" [x]
        mortal x = pApp "Mortal" [x] in
    ("socrates"
    , [ TestFormula
       { name = "all humans are mortal"
       , formula = for_all [V "x"] (human x .=>. mortal x)
       , expected = [ClausalNormalForm  [[((.~.) (human x)), mortal x]]] }
     , TestFormula
       { name = "socrates is human"
       , formula = for_all [V "x"] (socrates x .=>. human x)
       , expected = [ClausalNormalForm  [[(.~.) (socrates x), human x]]] }
     ])

{-
socratesConjectures =
    map (withKB socratesKB)
     [ TestFormula
       { formula = for_all [V "x"] (socrates x .=>. mortal x)
       , name = "socrates is mortal"
       , expected = [ FirstOrderFormula ((.~.) (((for_all [V "x"] ((pApp (Pr "Human") [var (V "x")]) .=>. ((pApp (Pr "Mortal") [var (V "x")])))) .&.
                                                 ((for_all [V "x"] ((pApp (Pr "Socrates") [var (V "x")]) .=>. ((pApp (Pr "Human") [var (V "x")])))))) .=>.
                                                ((for_all [V "x"] ((pApp (Pr "Socrates") [var (V "x")]) .=>. ((pApp (Pr "Mortal") [var (V "x")])))))))
                    , ClausalNormalForm  [[((.~.) (pApp (Pr "Human") [var (V "x2")])),(pApp (Pr "Mortal") [var (V "x2")])],
                                          [((.~.) (pApp (Pr "Socrates") [var (V "x2")])),(pApp (Pr "Human") [var (V "x2")])],
                                          [(pApp (Pr "Socrates") [fApp (Skolem 1) [var (V "x2"),var (V "x2")]])],
                                          [((.~.) (pApp (Pr "Mortal") [fApp (Skolem 1) [var (V "x2"),var (V "x2")]]))]]
                    , SatPropLogic True ]
       }
     , TestFormula
       { formula = (.~.) (for_all [V "x"] (socrates x .=>. mortal x))
       , name = "not (socrates is mortal)"
       , expected = [ SatPropLogic False
                    , FirstOrderFormula ((.~.) (((for_all [V "x"] ((pApp (Pr "Human") [var (V "x")]) .=>. ((pApp (Pr "Mortal") [var (V "x")])))) .&.
                                                 ((for_all [V "x"] ((pApp (Pr "Socrates") [var (V "x")]) .=>. ((pApp (Pr "Human") [var (V "x")])))))) .=>.
                                                (((.~.) (for_all [V "x"] ((pApp (Pr "Socrates") [var (V "x")]) .=>. ((pApp (Pr "Mortal") [var (V "x")]))))))))
                    -- [~human(x) | mortal(x)], [~socrates(Sk1(x,y)) | human(Sk1(x,y))], socrates(Sk1(x,y)), ~mortal(Sk1(x,y))
                    -- ~1 | 2, ~3 | 4, 3, ~5?
                    , ClausalNormalForm [[((.~.) (pApp (Pr "Human") [x])), (pApp (Pr "Mortal") [x])],
                                         [((.~.) (pApp (Pr "Socrates") [fApp (Skolem 1) [x,y]])), (pApp (Pr "Human") [fApp (Skolem 1) [x,y]])],
                                         [(pApp (Pr "Socrates") [fApp (Skolem 1) [x,y]])], [((.~.) (pApp (Pr "Mortal") [fApp (Skolem 1) [x,y]]))]]
                    , ClausalNormalForm [[((.~.) (pApp (Pr "Human") [var (V "x2")])), (pApp (Pr "Mortal") [var (V "x2")])],
                                         [((.~.) (pApp (Pr "Socrates") [var (V "x2")])), (pApp (Pr "Human") [var (V "x2")])],
                                         [((.~.) (pApp (Pr "Socrates") [var (V "x")])), (pApp (Pr "Mortal") [var (V "x")])]] ]
       }
     ]
-}

chang43KB = 
    let e = var (V "e")
        (x, y, z, u, v, w) = (var "x", var "y", var "z", var "u", var "v", var "w") in
    ("chang example 4.3"
    , [ TestFormula { name = "closure property"
                    , formula = for_all ["x", "y"] (exists ["z"] (pApp "P" [x,y,z]))
                    , expected = [] }
      , TestFormula { name = "associativity property"
                    , formula = for_all ["x", "y", "z", "u", "v", "w"] (pApp "P" [x, y, u] .&. pApp "P" [y, z, v] .&. pApp "P" [u, z, w] .=>. pApp "P" [x, v, w]) .&.
                                for_all ["x", "y", "z", "u", "v", "w"] (pApp "P" [x, y, u] .&. pApp "P" [y, z, v] .&. pApp "P" [x, v, w] .=>. pApp "P" [u, z, w])
                    , expected = [] }
      , TestFormula { name = "identity property"
                    , formula = (for_all ["x"] (pApp "P" [x,e,x])) .&. (for_all ["x"] (pApp "P" [e,x,x]))
                    , expected = [] }
      , TestFormula { name = "inverse property"
                    , formula = (for_all ["x"] (pApp "P" [x,fApp "i" [x], e])) .&. (for_all ["x"] (pApp "P" [fApp "i" [x], x, e]))
                    , expected = [] }
      ])

chang43Conjecture =
    let e = (var (V "e"))
        (x, u, v, w) = (var "x", var "u", var "v", var "w") in
    withKB chang43KB $
    TestFormula { name = "G is commutative"
                , formula = for_all ["x"] (pApp "P" [x, x, e] .=>. (for_all ["u", "v", "w"] (pApp "P" [u, v, w] .=>. pApp "P" [v, u, w]))) 
                , expected =
                    [ FirstOrderFormula 
                      ((.~.) (((for_all [V "x",V "y"] (exists [V "z"] (pApp (Pr "P") [var (V "x"),var (V "y"),var (V "z")]))) .&.
                               ((((for_all [V "x",V "y",V "z",V "u",V "v",V "w"]
                                   ((((pApp (Pr "P") [var (V "x"),var (V "y"),var (V "u")]) .&.
                                      ((pApp (Pr "P") [var (V "y"),var (V "z"),var (V "v")]))) .&.
                                     ((pApp (Pr "P") [var (V "u"),var (V "z"),var (V "w")]))) .=>.
                                    ((pApp (Pr "P") [var (V "x"),var (V "v"),var (V "w")])))) .&.
                                  ((for_all [V "x",V "y",V "z",V "u",V "v",V "w"]
                                    ((((pApp (Pr "P") [var (V "x"),var (V "y"),var (V "u")]) .&.
                                       ((pApp (Pr "P") [var (V "y"),var (V "z"),var (V "v")]))) .&.
                                      ((pApp (Pr "P") [var (V "x"),var (V "v"),var (V "w")]))) .=>.
                                     ((pApp (Pr "P") [var (V "u"),var (V "z"),var (V "w")])))))) .&.
                                 ((((for_all [V "x"] (pApp (Pr "P") [var (V "x"),var (V "e"),var (V "x")])) .&.
                                    ((for_all [V "x"] (pApp (Pr "P") [var (V "e"),var (V "x"),var (V "x")])))) .&.
                                   (((for_all [V "x"] (pApp (Pr "P") [var (V "x"),fApp (Fn "i") [var (V "x")],var (V "e")])) .&.
                                     ((for_all [V "x"] (pApp (Pr "P") [fApp (Fn "i") [var (V "x")],var (V "x"),var (V "e")])))))))))) .=>.
                              ((for_all [V "x"]
                                ((pApp (Pr "P") [var (V "x"),var (V "x"),var (V "e")]) .=>.
                                 ((for_all [V "u",V "v",V "w"]
                                   ((pApp (Pr "P") [var (V "u"),var (V "v"),var (V "w")]) .=>.
                                    ((pApp (Pr "P") [var (V "v"),var (V "u"),var (V "w")]))))))))))
                      -- (∀x ∀y ∃z P(x,y,z)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(u,z,w) | P(x,v,w)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(x,v,w) | P(u,z,w)) &
                      -- (∀x P(x,e,x)) &
                      -- (∀x P(e,x,x)) &
                      -- (∀x P(x,i[x],e)) &
                      -- (∀x P(i[x],x,e)) &
                      -- (∃x P(x,x,e) & (∃u∃v∃w P(u,v,w) & ~P(v,u,w)))
                    , NegationNormalForm 
                      (((for_all [V "x",V "y"] (exists [V "z"] (pApp (Pr "P") [var (V "x"),var (V "y"),var (V "z")]))) .&.
                        ((((for_all [V "x",V "y",V "z",V "u",V "v",V "w"]
                            (((((.~.) (pApp (Pr "P") [var (V "x"),var (V "y"),var (V "u")])) .|.
                               (((.~.) (pApp (Pr "P") [var (V "y"),var (V "z"),var (V "v")])))) .|.
                              (((.~.) (pApp (Pr "P") [var (V "u"),var (V "z"),var (V "w")])))) .|.
                             ((pApp (Pr "P") [var (V "x"),var (V "v"),var (V "w")])))) .&.
                           ((for_all [V "x",V "y",V "z",V "u",V "v",V "w"]
                             (((((.~.) (pApp (Pr "P") [var (V "x"),var (V "y"),var (V "u")])) .|.
                                (((.~.) (pApp (Pr "P") [var (V "y"),var (V "z"),var (V "v")])))) .|.
                               (((.~.) (pApp (Pr "P") [var (V "x"),var (V "v"),var (V "w")])))) .|.
                              ((pApp (Pr "P") [var (V "u"),var (V "z"),var (V "w")])))))) .&.
                          ((((for_all [V "x"] (pApp (Pr "P") [var (V "x"),var (V "e"),var (V "x")])) .&.
                             ((for_all [V "x"] (pApp (Pr "P") [var (V "e"),var (V "x"),var (V "x")])))) .&.
                            (((for_all [V "x"] (pApp (Pr "P") [var (V "x"),fApp (Fn "i") [var (V "x")],var (V "e")])) .&.
                              ((for_all [V "x"] (pApp (Pr "P") [fApp (Fn "i") [var (V "x")],var (V "x"),var (V "e")])))))))))) .&.
                       ((exists [V "x"] ((pApp (Pr "P") [var (V "x"),var (V "x"),var (V "e")]) .&.
                                         ((exists [V "u",V "v",V "w"]
                                           ((pApp (Pr "P") [var (V "u"),var (V "v"),var (V "w")]) .&.
                                            (((.~.) (pApp (Pr "P") [var (V "v"),var (V "u"),var (V "w")]))))))))))
                    , PrenexNormalForm
                      (for_all [V "x",V "y"]
                       (exists [V "z"]
                        (for_all [V "x2",V "y2",V "z2",V "u",V "v",V "w"]
                         (for_all [V "x2",V "y2",V "z2",V "u2",V "v2",V "w2"] 
                          (for_all [V "x3"]
                           (for_all [V "x3"]
                            (for_all [V "x3"]
                             (for_all [V "x3"]
                              (exists [V "x4"]
                               (exists [V "u3",V "v3",V "w3"]
                                (((pApp (Pr "P") [var (V "x"),var (V "y"),var (V "z")]) .&.
                                  ((((((((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u")])) .|.
                                        (((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v")])))) .|.
                                       (((.~.) (pApp (Pr "P") [var (V "u"),var (V "z2"),var (V "w")])))) .|.
                                      ((pApp (Pr "P") [var (V "x2"),var (V "v"),var (V "w")]))) .&.
                                     ((((((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u2")])) .|.
                                         (((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v2")])))) .|.
                                        (((.~.) (pApp (Pr "P") [var (V "x2"),var (V "v2"),var (V "w2")])))) .|.
                                       ((pApp (Pr "P") [var (V "u2"),var (V "z2"),var (V "w2")]))))) .&.
                                    ((((pApp (Pr "P") [var (V "x3"),var (V "e"),var (V "x3")]) .&.
                                       ((pApp (Pr "P") [var (V "e"),var (V "x3"),var (V "x3")]))) .&.
                                      (((pApp (Pr "P") [var (V "x3"),fApp (Fn "i") [var (V "x3")],var (V "e")]) .&.
                                        ((pApp (Pr "P") [fApp (Fn "i") [var (V "x3")],var (V "x3"),var (V "e")]))))))))) .&.
                                 (((pApp (Pr "P") [var (V "x4"),var (V "x4"),var (V "e")]) .&.
                                   (((pApp (Pr "P") [var (V "u3"),var (V "v3"),var (V "w3")]) .&.
                                     (((.~.) (pApp (Pr "P") [var (V "v3"),var (V "u3"),var (V "w3")]))))))))))))))))))
                    , SkolemNormalForm
                      (for_all [V "x",V "y"]
                       (for_all [V "x2",V "y2",V "z2",V "u",V "v",V "w"]
                        (for_all [V "x2",V "y2",V "z2",V "u2",V "v2",V "w2"]
                         (for_all [V "x3"]
                          (for_all [V "x3"]
                           (for_all [V "x3"]
                            (for_all [V "x3"]
                             (((pApp (Pr "P") [var (V "x"),var (V "y"),fApp (Skolem 1) [var (V "x"),var (V "y")]]) .&.
                               ((((((((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u")])) .|.
                                     (((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v")])))) .|.
                                    (((.~.) (pApp (Pr "P") [var (V "u"),var (V "z2"),var (V "w")])))) .|.
                                   ((pApp (Pr "P") [var (V "x2"),var (V "v"),var (V "w")]))) .&.
                                  ((((((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u2")])) .|.
                                      (((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v2")])))) .|.
                                     (((.~.) (pApp (Pr "P") [var (V "x2"),var (V "v2"),var (V "w2")])))) .|.
                                    ((pApp (Pr "P") [var (V "u2"),var (V "z2"),var (V "w2")]))))) .&.
                                 ((((pApp (Pr "P") [var (V "x3"),var (V "e"),var (V "x3")]) .&.
                                    ((pApp (Pr "P") [var (V "e"),var (V "x3"),var (V "x3")]))) .&.
                                   (((pApp (Pr "P") [var (V "x3"),fApp (Fn "i") [var (V "x3")],var (V "e")]) .&.
                                     ((pApp (Pr "P") [fApp (Fn "i") [var (V "x3")],var (V "x3"),var (V "e")]))))))))) .&.
                              (((pApp (Pr "P") [fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                var (V "e")]) .&.
                                (((pApp (Pr "P") [fApp (Skolem 3) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                  fApp (Skolem 4) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                  fApp (Skolem 5) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")]]) .&.
                                  (((.~.) (pApp (Pr "P") [fApp (Skolem 4) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                          fApp (Skolem 3) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                                          fApp (Skolem 5) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")]])))))))))))))))

                    , SkolemNumbers (S.fromList [1,2,3,4,5])
                    -- From our algorithm
                    , let a = fApp (Skolem 3) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")]
                          b = fApp (Skolem 4) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")]
                          c = fApp (Skolem 5) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")]
                      in 
                      ClausalNormalForm
                      [[(pApp (Pr "P") [var (V "x"),var (V "y"),fApp (Skolem 1) [var (V "x"),var (V "y")]])],
                       [((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u")])),
                        ((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v")])),
                        ((.~.) (pApp (Pr "P") [var (V "u"),var (V "z2"),var (V "w")])),
                        (pApp (Pr "P") [var (V "x2"),var (V "v"),var (V "w")])],
                       [((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u2")])),
                        ((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v2")])),
                        ((.~.) (pApp (Pr "P") [var (V "x2"),var (V "v2"),var (V "w2")])),
                        (pApp (Pr "P") [var (V "u2"),var (V "z2"),var (V "w2")])],
                       [(pApp (Pr "P") [var (V "x3"),var (V "e"),var (V "x3")])],
                       [(pApp (Pr "P") [var (V "e"),var (V "x3"),var (V "x3")])],
                       [(pApp (Pr "P") [var (V "x3"),fApp (Fn "i") [var (V "x3")],var (V "e")])],
                       [(pApp (Pr "P") [fApp (Fn "i") [var (V "x3")],var (V "x3"),var (V "e")])],
                       [(pApp (Pr "P") [fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                        fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x3"),var (V "x3"),var (V "x3"),var (V "x3")],
                                        var (V "e")])],
                       [(pApp (Pr "P") [a, b, c])],
                       [((.~.) (pApp (Pr "P") [b, a, c]))]]
                    -- From the book
{-
                    , let (a, b, c) = (fApp (V "a") [], fApp (V "b") [], fApp (V "c") []) in
                      ClausalNormalForm
                      [[(pApp "P" [var (V "x"),var (V "y"),fApp (Skolem 1) [var (V "x"),var (V "y")]])],
                       [((.~.) (pApp "P" [var (V "x"),var (V "y"),var (V "u")])),
                        ((.~.) (pApp "P" [var (V "y"),var (V "z"),var (V "v")])),
                        ((.~.) (pApp "P" [var (V "u"),var (V "z"),var (V "w")])),
                        (pApp "P" [var (V "x"),var (V "v"),var (V "w")])],
                       [((.~.) (pApp "P" [var (V "x"),var (V "y"),var (V "u")])),
                        ((.~.) (pApp "P" [var (V "y"),var (V "z"),var (V "v")])),
                        ((.~.) (pApp "P" [var (V "x"),var (V "v"),var (V "w")])),
                        (pApp "P" [var (V "u"),var (V "z"),var (V "w")])],
                       [(pApp "P" [var (V "x"),var (V "e"),var (V "x")])],
                       [(pApp "P" [var (V "e"),var (V "x"),var (V "x")])],
                       [(pApp "P" [var (V "x"),fApp (Fn "i") [var (V "x")],var (V "e")])],
                       [(pApp "P" [fApp (Fn "i") [var (V "x")],var (V "x"),var (V "e")])],
                       [(pApp "P" [var (V "x"),var (V "x"),var (V "e")])],
                       [(pApp "P" [a, b, c])],
                       [((.~.) (pApp "P" [b, a, c]))]]
-}
                    ]
                }

chang43ConjectureRenamed =
    let e = fApp "e" []
        (x, y, z, u, v, w) = (var "x", var "y", var "z", var "u", var "v", var "w")
        (u2, v2, w2, x2, y2, z2, u3, v3, w3, x3, y3, z3, x4, x5, x6, x7, x8) =
            (var "u2", var "v2", var "w2", var "x2", var "y2", var "z2", var "u3", var "v3", var "w3", var "x3", var "y3", var "z3", var "x4", var "x5", var "x6", var "x7", var "x8") in
    TestFormula { name = "chang 43 renamed"
                , formula = (.~.) ((for_all ["x", "y"] (exists ["z"] (pApp "P" [x,y,z])) .&.
                                    for_all ["x2", "y2", "z2", "u", "v", "w"] (pApp "P" [x2, y2, u] .&. pApp "P" [y2, z2, v] .&. pApp "P" [u, z2, w] .=>. pApp "P" [x2, v, w]) .&.
                                    for_all ["x3", "y3", "z3", "u2", "v2", "w2"] (pApp "P" [x3, y3, u2] .&. pApp "P" [y3, z3, v2] .&. pApp "P" [x3, v2, w2] .=>. pApp "P" [u2, z3, w2]) .&.
                                    for_all ["x4"] (pApp "P" [x4,e,x4]) .&.
                                    for_all ["x5"] (pApp "P" [e,x5,x5]) .&.
                                    for_all ["x6"] (pApp "P" [x6,fApp "i" [x6], e]) .&.
                                    for_all ["x7"] (pApp "P" [fApp "i" [x7], x7, e])) .=>.
                                   (for_all ["x8"] (pApp "P" [x8, x8, e] .=>. (for_all ["u3", "v3", "w3"] (pApp "P" [u3, v3, w3] .=>. pApp "P" [v3, u3, w3])))))
                , expected =
                    [ FirstOrderFormula
                      ((.~.) ((((((((for_all [V "x",V "y"] (exists [V "z"] (pApp (Pr "P") [var (V "x"),var (V "y"),var (V "z")]))) .&.
                                    ((for_all [V "x2",V "y2",V "z2",V "u",V "v",V "w"] ((((pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u")]) .&.
                                                                                          ((pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v")]))) .&.
                                                                                         ((pApp (Pr "P") [var (V "u"),var (V "z2"),var (V "w")]))) .=>.
                                                                                        ((pApp (Pr "P") [var (V "x2"),var (V "v"),var (V "w")])))))) .&.
                                   ((for_all [V "x3",V "y3",V "z3",V "u2",V "v2",V "w2"] ((((pApp (Pr "P") [var (V "x3"),var (V "y3"),var (V "u2")]) .&.
                                                                                            ((pApp (Pr "P") [var (V "y3"),var (V "z3"),var (V "v2")]))) .&.
                                                                                           ((pApp (Pr "P") [var (V "x3"),var (V "v2"),var (V "w2")]))) .=>.
                                                                                          ((pApp (Pr "P") [var (V "u2"),var (V "z3"),var (V "w2")])))))) .&.
                                  ((for_all [V "x4"] (pApp (Pr "P") [var (V "x4"),fApp "e" [],var (V "x4")])))) .&.
                                 ((for_all [V "x5"] (pApp (Pr "P") [fApp "e" [],var (V "x5"),var (V "x5")])))) .&.
                                ((for_all [V "x6"] (pApp (Pr "P") [var (V "x6"),fApp (Fn "i") [var (V "x6")],fApp "e" []])))) .&.
                               ((for_all [V "x7"] (pApp (Pr "P") [fApp (Fn "i") [var (V "x7")],var (V "x7"),fApp "e" []])))) .=>.
                              ((for_all [V "x8"] ((pApp (Pr "P") [var (V "x8"),var (V "x8"),fApp "e" []]) .=>.
                                                  ((for_all [V "u3",V "v3",V "w3"] ((pApp (Pr "P") [var (V "u3"),var (V "v3"),var (V "w3")]) .=>.
                                                                                    ((pApp (Pr "P") [var (V "v3"),var (V "u3"),var (V "w3")]))))))))))
                    , ClausalNormalForm
                      [[(pApp (Pr "P") [var (V "x"),var (V "y"),fApp (Skolem 1) [var (V "x"),var (V "y")]])],
                       [((.~.) (pApp (Pr "P") [var (V "x2"),var (V "y2"),var (V "u")])),
                        ((.~.) (pApp (Pr "P") [var (V "y2"),var (V "z2"),var (V "v")])),
                        ((.~.) (pApp (Pr "P") [var (V "u"),var (V "z2"),var (V "w")])),
                        (pApp (Pr "P") [var (V "x2"),var (V "v"),var (V "w")])],
                       [((.~.) (pApp (Pr "P") [var (V "x3"),var (V "y3"),var (V "u2")])),
                        ((.~.) (pApp (Pr "P") [var (V "y3"),var (V "z3"),var (V "v2")])),
                        ((.~.) (pApp (Pr "P") [var (V "x3"),var (V "v2"),var (V "w2")])),
                        (pApp (Pr "P") [var (V "u2"),var (V "z3"),var (V "w2")])],
                       [(pApp (Pr "P") [var (V "x4"),fApp "e" [],var (V "x4")])],
                       [(pApp (Pr "P") [fApp "e" [],var (V "x5"),var (V "x5")])],
                       [(pApp (Pr "P") [var (V "x6"),fApp (Fn "i") [var (V "x6")],fApp "e" []])],
                       [(pApp (Pr "P") [fApp (Fn "i") [var (V "x7")],var (V "x7"),fApp "e" []])],
                       [(pApp (Pr "P") [fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                        fApp (Skolem 2) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                        fApp "e" []])],
                       [(pApp (Pr "P") [fApp (Skolem 3) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                        fApp (Skolem 4) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                        fApp (Skolem 5) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")]])],
                       [((.~.) (pApp (Pr "P") [fApp (Skolem 4) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                               fApp (Skolem 3) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")],
                                               fApp (Skolem 5) [var (V "x"),var (V "y"),var (V "x2"),var (V "y2"),var (V "z2"),var (V "u"),var (V "v"),var (V "w"),var (V "x3"),var (V "y3"),var (V "z3"),var (V "u2"),var (V "v2"),var (V "w2"),var (V "x4"),var (V "x5"),var (V "x6"),var (V "x7")]]))]]
                    ]
                }

withKB :: (String, [TestFormula]) -> TestFormula -> TestFormula
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

proofs =
    let dog = pApp "Dog" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        cat = pApp "Cat" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        owns = pApp "Owns" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        kills = pApp "Kills" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        animal = pApp "Animal" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        animalLover = pApp "AnimalLover" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        socrates = pApp "Socrates" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        human = pApp "Human" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction
        mortal = pApp "Mortal" :: [C.Term V AtomicFunction] -> C.Sentence V Pr AtomicFunction

        jack :: C.Term V AtomicFunction
        jack = fApp "Jack" []
        tuna :: C.Term V AtomicFunction
        tuna = fApp "Tuna" []
        curiosity :: C.Term V AtomicFunction
        curiosity = fApp "Curiosity" [] in

    [ TestProof
      { proofName = "jack kills tuna"
      , proofKnowledge = (fst animalKB, map (convertFOF id id id . formula) (snd animalKB))
      , conjecture = kills [jack, tuna]
      , proofExpected = 
          [ ChiouResult (False,
                         [(INF [NFPredicate (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []]] [],[]),
                          (INF [] [NFPredicate (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []]],[]),
                          (INF [NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [fApp (Fn "Curiosity") []]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [fApp (Fn "Curiosity") []]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "AnimalLover") [fApp (Fn "Curiosity") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")],NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")]] [],[])])
          ]
      }
    , TestProof
      { proofName = "curiosity kills tuna"
      , proofKnowledge = (fst animalKB, map (convertFOF id id id . formula) (snd animalKB))
      , conjecture = kills [curiosity, tuna]
      , proofExpected =
          [ ChiouResult (True,
                         [(INF [NFPredicate (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []]] [],[]),
                          (INF [] [NFPredicate (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [fApp (Fn "Jack") []]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [fApp (Fn "Jack") []]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "AnimalLover") [fApp (Fn "Jack") []]] [],[]),
                          (INF [NFPredicate (Pr "Animal") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []],NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")],NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")],NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")]] [],[]),
                          (INF [NFPredicate (Pr "Cat") [fApp (Fn "Tuna") []]] [],[]),
                          (INF [NFPredicate (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")]] [],[]),
                          (INF [NFPredicate (Pr "Dog") [var (V "y2")]] [],[]),(INF [] [],[])]) ]
      }
{-
  -- Seems not to terminate
    , let (x, u, v, w, e) = (var "x", var "u", var "v", var "w", var "e") in
      TestProof
      { proofName = "chang example 4.3"
      , proofKnowledge = (fst chang43KB, map (convertFOF id id id . formula) (snd chang43KB))
      , conjecture = for_all ["x"] (pApp "P" [x, x, e] .=>. (for_all ["u", "v", "w"] (pApp "P" [u, v, w] .=>. pApp "P" [v, u, w])))
      , proofExpected =
          [ChiouResult (True, [])]
      }
-}
    , let x = var "x" in
      TestProof
      { proofName = "socrates is mortal"
      , proofKnowledge = (fst socratesKB, map (convertFOF id id id . formula) (snd socratesKB))
      , conjecture = for_all ["x"] (socrates [x] .=>. mortal [x])
      , proofExpected = 
          [ChiouResult (True,
                        [(INF [] [NFPredicate (Pr "Socrates") [fApp (Skolem 1) []]],[]),
                         (INF [NFPredicate (Pr "Mortal") [fApp (Skolem 1) []]] [],[]),
                         (INF [] [NFPredicate (Pr "Human") [fApp (Skolem 1) []]],[]),
                         (INF [NFPredicate (Pr "Human") [fApp (Skolem 1) []]] [],[]),
                         (INF [] [NFPredicate (Pr "Mortal") [fApp (Skolem 1) []]],[]),
                         (INF [] [],[])])]
      }
    , let x = var "x" in
      TestProof
      { proofName = "socrates is not mortal"
      , proofKnowledge = (fst socratesKB, map (convertFOF id id id . formula) (snd socratesKB))
      , conjecture = (.~.) (for_all ["x"] (socrates [x] .=>. mortal [x]))
      , proofExpected = 
          [ChiouResult (False
                       ,[(INF [NFPredicate (Pr "Socrates") [var (V "x")]]
                              [NFPredicate (Pr "Mortal") [var (V "x")]],
                          [(V "x",var (V "x"))])])]
      }
    , let x = var "x" in
      TestProof
      { proofName = "socrates exists and is is not mortal"
      , proofKnowledge = (fst socratesKB, map (convertFOF id id id . formula) (snd socratesKB))
      , conjecture = (.~.) (exists ["x"] (socrates [x]) .&. for_all ["x"] (socrates [x] .=>. mortal [x]))
      , proofExpected = 
          [ChiouResult (False,
                        [(INF []                                           [NFPredicate (Pr "Socrates") [fApp (Skolem 1) []]], []),
                         (INF [NFPredicate (Pr "Socrates") [var (V "x2")]] [NFPredicate (Pr "Mortal") [var (V "x2")]],         [(V "x2",var (V "x2"))]),
                         (INF []                                           [NFPredicate (Pr "Human") [fApp (Skolem 1) []]],    []),
                         (INF []                                           [NFPredicate (Pr "Mortal") [fApp (Skolem 1) []]],   [(V "x2",fApp (Skolem 1) [])])])]
      }
    ]
