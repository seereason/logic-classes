{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, NoMonomorphismRestriction, OverloadedStrings, RankNTypes, ScopedTypeVariables  #-}
{-# OPTIONS -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Test.Data
    ( allFormulas
    , formulas
    , proofs
    , animalKB
    , animalConjectures
    , chang43KB
    , chang43Conjecture
    , chang43ConjectureRenamed
    ) where

import Data.Generics (Typeable)
import Data.Map (fromList)
import qualified Data.Set as S
import qualified Logic.Instances.Chiou as C
import Logic.FirstOrder (FirstOrderLogic(..), Term(..), Skolem(toSkolem), convertFOF)
import Logic.Implicative (Implicative(..))
import Logic.Instances.Native (ImplicativeNormalForm(..))
import Logic.Logic (Logic(..), Boolean(..))
import Logic.Monad (WithId(..))
import Test.Types (TestFormula(..), TestProof(..), Expected(..), ProofExpected(..))

allFormulas :: forall formula term v p f. (FirstOrderLogic formula term v p f, Typeable formula) =>
               [TestFormula formula]
allFormulas = (formulas ++
               concatMap snd [animalKB, chang43KB] ++
               animalConjectures ++
               [chang43Conjecture, chang43ConjectureRenamed])

formulas :: forall formula term v p f. FirstOrderLogic formula term v p f =>
            [TestFormula formula]
formulas =
    let n = (.~.) :: Logic formula => formula -> formula
        p = pApp "p" :: [term] -> formula
        q = pApp "q" :: [term] -> formula
        r = pApp "r" :: [term] -> formula
        s = pApp "s" :: [term] -> formula
        t = pApp "t" :: [term] -> formula
        p0 = p [] :: formula
        q0 = q [] :: formula
        r0 = r [] :: formula
        s0 = s [] :: formula
        t0 = t [] :: formula
        (x, y, z, u, v, w) :: (term, term, term, term, term, term) =
                              (var "x", var "y", var "z", var "u", var "v", var "w") in
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
      { formula = pApp "p" []
      , name = "p"
      , expected = [ClausalNormalForm  [[pApp "p" []]]] }
    , TestFormula
      { formula = pApp "p" [] .&. ((.~.) (pApp "p" []))
      , name = "p&~p"
      , expected = [ClausalNormalForm  [[(pApp "p" [])],[((.~.) (pApp "p" []))]]] }
    , TestFormula
      { formula = pApp "p" [var "x"]
      , name = "p[x]"
      , expected = [ClausalNormalForm  [[pApp "p" [x]]]] }
    , let f = pApp "f"
          q = pApp "q" in
      TestFormula
      { name = "iff"
      , formula = for_all ["x"] (for_all ["y"] (q [x, y] .<=>. for_all ["z"] (f [z, x] .<=>. f [z, y])))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp "q" [var "x",var "y"])),
                      ((.~.) (pApp "f" [var "z",var "x"])),
                      (pApp "f" [var "z",var "y"])],
                     [((.~.) (pApp "q" [var "x",var "y"])),
                      ((.~.) (pApp "f" [var "z",var "y"])),
                      (pApp "f" [var "z",var "x"])],
                     [(pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "x"]),
                      (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "y"]),
                      (pApp "q" [var "x",var "y"])],
                     [((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "y"])),
                      (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "y"]),
                      (pApp "q" [var "x",var "y"])],
                     [(pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "x"]),
                      ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "x"])),
                      (pApp "q" [var "x",var "y"])],
                     [((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "y"])),
                      ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "y",var "z"],var "x"])),
                      (pApp "q" [var "x",var "y"])]]]
      }
    , TestFormula
      { name = "move quantifiers out"
      , formula = (for_all ["x"] (pApp "p" [x]) .&. (pApp "q" [x]))
      , expected = [PrenexNormalForm (for_all ["x"] ((pApp "p" [var ("x")]) .&. ((pApp "q" [var ("x")]))))]
      }
    , TestFormula
      { name = "skolemize1"
      , formula = (exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w]))))))
      , expected = [SkolemNormalForm
                    (for_all ["y"]
                     (for_all ["z"]
                      (for_all ["v"]
                       (pApp "P" [fApp (toSkolem 1) [],
                                       var ("y"),
                                       var ("z"),
                                       fApp (toSkolem 2) [var ("y"),var ("z")],
                                       var ("v"),
                                       fApp (toSkolem 3) [var ("y"),var ("z"),var ("v")]]))))]
      }
    , TestFormula
      { name = "skolemize2"
      , formula = exists ["x"] (for_all ["y"] (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (for_all ["y"] (pApp ("loves") [fApp (toSkolem 1) [],y]))]
      }
    , TestFormula
      { name = "skolemize3"
      , formula = for_all ["y"] (exists ["x"] (pApp "loves" [x, y]))
      , expected = [SkolemNormalForm (for_all ["y"] (pApp ("loves") [fApp (toSkolem 1) [y],y]))]
      }
    , TestFormula
      { formula = exists ["x"] (for_all ["y", "z"] (exists ["u"] (for_all ["v"] (exists ["w"] (pApp "P" [x, y, z, u, v, w])))))
      , name = "chang example 4.1"
      , expected = [ SkolemNormalForm (for_all ["y"] (for_all ["z"] (for_all ["v"] (pApp "P" [fApp (toSkolem 1) [],var ("y"),var ("z"),fApp (toSkolem 2) [var ("y"),var ("z")],var ("v"),fApp (toSkolem 3) [var ("y"),var ("z"),var ("v")]])))) ] }
    , TestFormula
      { name = "chang example 4.2"
      -- ∀x ∃y∃z ~P(x,y) & Q(x,z) | R(x,y,z)
      , formula = for_all ["x"] (exists ["y", "z"] (((((.~.) (pApp "P" [x, y])) .&. pApp "Q" [x, z]) .|. pApp "R" [x, y, z])))
      -- ∀x ~P(x,Sk1[x]) | R(x,Sk1[x],Sk2[x]) & Q(x,Sk2[x]) | R(x,Sk1[x],Sk2[x])
      , expected = [ SkolemNormalForm (for_all ["x"] ((((.~.) (pApp "P" [x, fApp (toSkolem 1) [x]])) .|.
                                                       (pApp "R" [x, fApp (toSkolem 1) [x], fApp (toSkolem 2) [x]])) .&.
                                                      ((pApp "Q" [x, fApp (toSkolem 2) [x]]) .|.
                                                       (pApp "R" [x, fApp (toSkolem 1) [x], fApp (toSkolem 2) [x]])))) ]
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
                    (((((.~.) (pApp "q" [var "x",var "y"])) .|.
                       (((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])) .|.
                        (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"]))) .&.
                      (((.~.) (pApp "q" [var "x",var "y"])) .|.
                       (((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"])))) .&. 
                     (((((pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]) .|.
                         (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp "q" [var "x",var "y"])) .&.
                       ((((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                         (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                        (pApp "q" [var "x",var "y"]))) .&.
                      ((((pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]) .|.
                         ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]))) .|.
                        (pApp "q" [var "x",var "y"])) .&.
                       ((((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "y"])) .|.
                         ((.~.) (pApp "f" [fApp (toSkolem 1) [var "x",var "x",var "y",var "z"],var "x"]))) .|.
                        (pApp "q" [var "x",var "y"])))))]
      }
    , let (x, y) = (var "x", var "y")
          (x', y') = (var "x", var "y") in
      TestFormula
      { name = "convert to Chiou 1"
      , formula = exists ["x"] (x .=. y)
      , expected = [ConvertToChiou (exists ["x"] (x' .=. y'))]
      }
    , let -- s :: [ATerm] -> Formula
          s = pApp "s"
          --s' :: [C.CTerm V AtomicFunction] -> C.Sentence V Pr AtomicFunction
          s' = pApp "s"
          --x' :: C.CTerm V AtomicFunction
          x' = var "x"
          --y' :: C.CTerm V AtomicFunction
          y' = var "y" in
      TestFormula
      { name = "convert to Chiou 2"
      , formula = s [fApp ("a") [x, y]]
      , expected = [ConvertToChiou (s' [fApp "a" [x', y']])]
      }
    , let s :: [term] -> formula
          s = pApp "s"
          h :: [term] -> formula
          h = pApp "h"
          m :: [term] -> formula
          m = pApp "m"
          s' :: [term] -> formula
          s' = pApp "s"
          h' :: [term] -> formula
          h' = pApp "h"
          m' :: [term] -> formula
          m' = pApp "m"
          x' :: term
          x' = var "x" in
      TestFormula
      { name = "convert to Chiou 3"
      , formula = for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
      , expected = [ConvertToChiou (for_all ["x"] (((s' [x'] .=>. h' [x']) .&. (h' [x'] .=>. m' [x'])) .=>. (s' [x'] .=>. m' [x'])))]
      }
    , let taller :: term -> term -> formula
          taller a b = pApp ("taller" :: p) [a, b]
          wise :: term -> formula
          wise a = pApp ("wise" :: p) [a] in
      TestFormula
      { name = "cnf test 1"
      , formula = for_all ["y"] (for_all ["x"] (taller y x .|. wise x) .=>. wise y)
      , expected = [ClausalNormalForm
                    [[(.~.) (taller (var "y") (fApp (toSkolem 1) [var "y"])), wise y],
                     [(.~.) (wise (fApp (toSkolem 1) [var "y"])), wise (var "y")]]]
      }
    , TestFormula
      { name = "cnf test 2"
      , formula = ((.~.) (exists ["x"] (pApp "s" [x] .&. pApp "q" [x])))
      , expected = [ClausalNormalForm [[((.~.) (pApp "s" [var "x"])),((.~.) (pApp "q" [var "x"]))]]]
      }
    , TestFormula
      { name = "cnf test 3"
      , formula = (for_all ["x"] (p [x] .=>. (q [x] .|. r [x])))
      , expected = [ClausalNormalForm [[((.~.) (pApp "p" [var "x"])),(pApp "q" [var "x"]),(pApp "r" [var "x"])]]]
      }
    , TestFormula
      { name = "cnf test 4"
      , formula = ((.~.) (exists ["x"] (p [x] .=>. exists ["y"] (q [y]))))
      , expected = [ClausalNormalForm [[(pApp "p" [var "x"])],[((.~.) (pApp "q" [var "y"]))]]]
      }
    , TestFormula
      { name = "cnf test 5"
      , formula = (for_all ["x"] (q [x] .|. r [x] .=>. s [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp "q" [var "x"])),(pApp "s" [var "x"])],[((.~.) (pApp "r" [var "x"])),(pApp "s" [var "x"])]]]
      }
    , TestFormula
      { name = "cnf test 6"
      , formula = (exists ["x"] (p0 .=>. pApp "f" [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp "p" [])),(pApp "f" [fApp (toSkolem 1) []])]]]
      }
    , TestFormula
      { name = "cnf test 7"
      , formula = (exists ["x"] (p0 .<=>. pApp "f" [x]))
      , expected = [ClausalNormalForm [[((.~.) (pApp "p" [])),(pApp "f" [fApp (toSkolem 1) []])],[((.~.) (pApp "f" [fApp (toSkolem 1) []])),(pApp "p" [])]]]
      }
    , TestFormula
      { name = "cnf test 8"
      , formula = (for_all ["z"] (exists ["y"] (for_all ["x"] (pApp "f" [x, y] .<=>. (pApp "f" [x, z] .&. ((.~.) (pApp "f" [x, x])))))))
      , expected = [ClausalNormalForm 
                    [[((.~.) (pApp "f" [var "x",fApp (toSkolem 1) [var "z"]])),(pApp "f" [var "x",var "z"])],
                     [((.~.) (pApp "f" [var "x",fApp (toSkolem 1) [var "z"]])),((.~.) (pApp "f" [var "x",var "x"]))],
                     [((.~.) (pApp "f" [var "x",var "z"])),(pApp "f" [var "x",var "x"]),(pApp "f" [var "x",fApp (toSkolem 1) [var "z"]])]]]
      }
    , TestFormula
      { name = "cnf test 9"
      , formula = (for_all ["x"] (for_all ["x"] (for_all ["y"] (q [x, y] .<=>. for_all ["z"] (pApp "f" [z, x] .<=>. pApp "f" [z, y])))))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp "q" [var ("x"),var ("y")])),((.~.) (pApp "f" [var ("z"),var ("x")])),(pApp "f" [var ("z"),var ("y")])],
                     [((.~.) (pApp "q" [var ("x"),var ("y")])),((.~.) (pApp "f" [var ("z"),var ("y")])),(pApp "f" [var ("z"),var ("x")])],
                     [(pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("x")]),(pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("y")]),(pApp "q" [var ("x"),var ("y")])],
                     [((.~.) (pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("y")])),(pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("y")]),(pApp "q" [var ("x"),var ("y")])],
                     [(pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("x")]),((.~.) (pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("x")])),(pApp "q" [var ("x"),var ("y")])],
                     [((.~.) (pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("y")])),((.~.) (pApp "f" [fApp (toSkolem 1) [var ("x2"),var ("x"),var ("y"),var ("z")],var ("x")])),(pApp "q" [var ("x"),var ("y")])]]]
      }
    , TestFormula
      { name = "cnf test 10"
      , formula = (for_all ["x"] (exists ["y"] ((p [x, y] .<=. for_all ["x"] (exists ["z"] (q [y, x, z]) .=>. r [y])))))
      , expected = [ClausalNormalForm
                    [[(pApp "q" [fApp (toSkolem 1) [var ("x2")],fApp (toSkolem 2) [var ("x2")],fApp (toSkolem 3) [var ("x2")]]),
                      (pApp "p" [var ("x2"),fApp (toSkolem 1) [var ("x2")]])],
                     [((.~.) (pApp "r" [fApp (toSkolem 1) [var ("x2")]])),
                      (pApp "p" [var ("x2"),fApp (toSkolem 1) [var ("x2")]])]]]
      }
    , TestFormula
      { name = "cnf test 11"
      , formula = (for_all ["x"] (for_all ["z"] (p [x, z] .=>. exists ["y"] ((.~.) (q [x, y] .|. ((.~.) (r [y, z])))))))
      , expected = [ClausalNormalForm
                    [[((.~.) (pApp "p" [var "x",var "z"])),((.~.) (pApp "q" [var "x",fApp (toSkolem 1) [var "x",var "z"]]))],
                     [((.~.) (pApp "p" [var "x",var "z"])),(pApp "r" [fApp (toSkolem 1) [var "x",var "z"],var "z"])]]]
      }
    , TestFormula
      { name = "cnf test 12"
      , formula = ((p0 .=>. q0) .=>. (((.~.) r0) .=>. (s0 .&. t0)))
      , expected = [ClausalNormalForm
                    [[(pApp "p" []),(pApp "r" []),(pApp "s" [])],
                     [((.~.) (pApp "q" [])),(pApp "r" []),(pApp "s" [])],
                     [(pApp "p" []),(pApp "r" []),(pApp "t" [])],
                     [((.~.) (pApp "q" [])),(pApp "r" []),(pApp "t" [])]]]
      }
    ]

animalKB :: forall formula term v p f. FirstOrderLogic formula term v p f =>
            (String, [TestFormula formula])
animalKB =
    let x = var "x"
        y = var "y"
        dog = pApp "Dog" -- :: [ATerm] -> Formula
        cat = pApp "Cat" -- :: [ATerm] -> Formula
        owns = pApp "Owns" -- :: [ATerm] -> Formula
        kills = pApp "Kills" -- :: [ATerm] -> Formula
        animal = pApp "Animal" -- :: [ATerm] -> Formula
        animalLover = pApp "AnimalLover" -- :: [ATerm] -> Formula
        jack = fApp "Jack" [] -- :: ATerm
        tuna = fApp "Tuna" [] -- :: ATerm
        curiosity = fApp "Curiosity" [] {- :: ATerm -} in
    ("animal"
    , [ TestFormula
       { formula = exists ["x"] (dog [x] .&. owns [jack, x]) -- [[Pos 1],[Pos 2]]
       , name = "jack owns a dog"
       , expected = [ClausalNormalForm  [[(pApp "Dog" [fApp (toSkolem 1) []])],[(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])]]]
       -- owns(jack,sK0)
       -- dog (SK0)
                   }
     , TestFormula
       { formula = for_all ["x"] ((exists ["y"] (dog [y] .&. (owns [x, y]))) .=>. (animalLover [x])) -- [[Neg 1,Neg 2,Pos 3]]
       , name = "dog owners are animal lovers"
       , expected = [ PrenexNormalForm (for_all ["x"] (for_all ["y"] ((((.~.) (pApp "Dog" [var "y"])) .|.
                                                                           (((.~.) (pApp "Owns" [var "x",var "y"])))) .|.
                                                                          ((pApp "AnimalLover" [var "x"])))))
                    , ClausalNormalForm [[((.~.) (pApp "Dog" [var "y"])),((.~.) (pApp "Owns" [var "x",var "y"])),(pApp "AnimalLover" [var "x"])]] ]
       -- animalLover(X0) | ~owns(X0,sK1(X0)) | ~dog(sK1(X0))
       }
     , TestFormula
       { formula = for_all ["x"] (animalLover [x] .=>. (for_all ["y"] ((animal [y]) .=>. ((.~.) (kills [x, y]))))) -- [[Neg 3,Neg 4,Neg 5]]
       , name = "animal lovers don't kill animals"
       , expected = [ClausalNormalForm  [[((.~.) (pApp "AnimalLover" [var "x"])),((.~.) (pApp "Animal" [var "y"])),((.~.) (pApp "Kills" [var "x",var "y"]))]]]
       -- ~kills(X0,X2) | ~animal(X2) | ~animalLover(sK2(X0))
       }
     , TestFormula
       { formula = (kills [jack, tuna]) .|. (kills [curiosity, tuna]) -- [[Pos 5,Pos 5]]
       , name = "Either jack or curiosity kills tuna"
       , expected = [ClausalNormalForm  [[(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []]),(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []])]]]
       -- kills(curiosity,tuna) | kills(jack,tuna)
       }
     , TestFormula
       { formula = cat [tuna] -- [[Pos 6]]
       , name = "tuna is a cat"
       , expected = [ClausalNormalForm  [[(pApp "Cat" [fApp "Tuna" []])]]]
       -- cat(tuna)
       }
     , TestFormula
       { formula = for_all ["x"] ((cat [x]) .=>. (animal [x])) -- [[Neg 6,Pos 4]]
       , name = "a cat is an animal"
       , expected = [ClausalNormalForm  [[((.~.) (pApp "Cat" [var "x"])),(pApp "Animal" [var "x"])]]]
       -- animal(X0) | ~cat(X0)
       }
     ])

animalConjectures :: forall formula term v p f. FirstOrderLogic formula term v p f => [TestFormula formula]
animalConjectures =
    let kills = pApp "Kills" :: [term] -> formula
        jack = fApp "Jack" [] :: term
        tuna = fApp "Tuna" [] :: term
        curiosity = fApp "Curiosity" [] :: term in

    map (withKB animalKB) $
     [ TestFormula
       { formula = kills [jack, tuna]             -- False
       , name = "jack kills tuna"
       , expected =
           [ FirstOrderFormula ((.~.) (((exists ["x"] ((pApp "Dog" [var ("x")]) .&. ((pApp "Owns" [fApp ("Jack") [],var ("x")])))) .&.
                                        (((for_all ["x"] ((exists ["y"] ((pApp "Dog" [var ("y")]) .&. ((pApp "Owns" [var ("x"),var ("y")])))) .=>.
                                                          ((pApp "AnimalLover" [var ("x")])))) .&.
                                          (((for_all ["x"] ((pApp "AnimalLover" [var ("x")]) .=>.
                                                            ((for_all ["y"] ((pApp "Animal" [var ("y")]) .=>.
                                                                             (((.~.) (pApp "Kills" [var ("x"),var ("y")])))))))) .&.
                                            ((((pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]) .|. ((pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []]))) .&.
                                              (((pApp "Cat" [fApp ("Tuna") []]) .&.
                                                ((for_all ["x"] ((pApp "Cat" [var ("x")]) .=>.
                                                                 ((pApp "Animal" [var ("x")])))))))))))))) .=>.
                                       ((pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]))))

           , PrenexNormalForm
             (exists ["x"]
              (for_all ["x2"]
               (for_all ["y"]
                (for_all ["x3"]
                 (for_all ["y2"]
                  (for_all ["x4"]
                   ((((pApp "Dog" [var ("x")]) .&.
                      ((pApp "Owns" [fApp ("Jack") [],var ("x")]))) .&.
                     ((((((.~.) (pApp "Dog" [var ("y")])) .|.
                         (((.~.) (pApp "Owns" [var ("x2"),var ("y")])))) .|.
                        ((pApp "AnimalLover" [var ("x2")]))) .&.
                       (((((.~.) (pApp "AnimalLover" [var ("x3")])) .|.
                          ((((.~.) (pApp "Animal" [var ("y2")])) .|.
                            (((.~.) (pApp "Kills" [var ("x3"),var ("y2")])))))) .&.
                         ((((pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]) .|.
                            ((pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []]))) .&.
                           (((pApp "Cat" [fApp ("Tuna") []]) .&.
                             ((((.~.) (pApp "Cat" [var ("x4")])) .|.
                               ((pApp "Animal" [var ("x4")]))))))))))))) .&.
                    (((.~.) (pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]))))))))))

           , ClausalNormalForm
             [[(pApp "Dog" [fApp (toSkolem 1) []])],
              [(pApp "Owns" [fApp ("Jack") [],fApp (toSkolem 1) []])],
              [((.~.) (pApp "Dog" [var ("y")])),
               ((.~.) (pApp "Owns" [var ("x2"),var ("y")])),
               (pApp "AnimalLover" [var ("x2")])],
              [((.~.) (pApp "AnimalLover" [var ("x3")])),
               ((.~.) (pApp "Animal" [var ("y2")])),
               ((.~.) (pApp "Kills" [var ("x3"),var ("y2")]))],
              [(pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]),
               (pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []])],
              [(pApp "Cat" [fApp ("Tuna") []])],
              [((.~.) (pApp "Cat" [var ("x4")])),
               (pApp "Animal" [var ("x4")])],
              [((.~.) (pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]))]]
           , SatPropLogic False ]
       }
     , TestFormula
       { formula = kills [curiosity, tuna]        -- True
       , name = "curiosity kills tuna"
       , expected =
           [ ClausalNormalForm
             [[(pApp "Dog" [fApp (toSkolem 1) []])],
              [(pApp "Owns" [fApp ("Jack") [],fApp (toSkolem 1) []])],
              [((.~.) (pApp "Dog" [var ("y")])),
               ((.~.) (pApp "Owns" [var ("x2"),var ("y")])),
               (pApp "AnimalLover" [var ("x2")])],
              [((.~.) (pApp "AnimalLover" [var ("x3")])),
               ((.~.) (pApp "Animal" [var ("y2")])),
               ((.~.) (pApp "Kills" [var ("x3"),var ("y2")]))],
              [(pApp "Kills" [fApp ("Jack") [],fApp ("Tuna") []]),
               (pApp "Kills" [fApp ("Curiosity") [],fApp ("Tuna") []])],
              [(pApp "Cat" [fApp ("Tuna") []])],
              [((.~.) (pApp "Cat" [var ("x4")])),
               (pApp "Animal" [var ("x4")])],
              [((.~.) (pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]))]]
           , SatPropLogic True ]
       }
     ]

socratesKB =
    let x = var "x"
        socrates x = pApp "Socrates" [x]
        human x = pApp "Human" [x]
        mortal x = pApp "Mortal" [x] in
    ("socrates"
    , [ TestFormula
       { name = "all humans are mortal"
       , formula = for_all ["x"] (human x .=>. mortal x)
       , expected = [ClausalNormalForm  [[((.~.) (human x)), mortal x]]] }
     , TestFormula
       { name = "socrates is human"
       , formula = for_all ["x"] (socrates x .=>. human x)
       , expected = [ClausalNormalForm  [[(.~.) (socrates x), human x]]] }
     ])

{-
socratesConjectures =
    map (withKB socratesKB)
     [ TestFormula
       { formula = for_all [V "x"] (socrates x .=>. mortal x)
       , name = "socrates is mortal"
       , expected = [ FirstOrderFormula ((.~.) (((for_all [V "x"] ((pApp "Human" [var "x"]) .=>. ((pApp "Mortal" [var "x"])))) .&.
                                                 ((for_all [V "x"] ((pApp "Socrates" [var "x"]) .=>. ((pApp "Human" [var "x"])))))) .=>.
                                                ((for_all [V "x"] ((pApp "Socrates" [var "x"]) .=>. ((pApp "Mortal" [var "x"])))))))
                    , ClausalNormalForm  [[((.~.) (pApp "Human" [var "x2"])),(pApp "Mortal" [var "x2"])],
                                          [((.~.) (pApp "Socrates" [var "x2"])),(pApp "Human" [var "x2"])],
                                          [(pApp "Socrates" [fApp (toSkolem 1) [var "x2",var "x2"]])],
                                          [((.~.) (pApp "Mortal" [fApp (toSkolem 1) [var "x2",var "x2"]]))]]
                    , SatPropLogic True ]
       }
     , TestFormula
       { formula = (.~.) (for_all [V "x"] (socrates x .=>. mortal x))
       , name = "not (socrates is mortal)"
       , expected = [ SatPropLogic False
                    , FirstOrderFormula ((.~.) (((for_all [V "x"] ((pApp "Human" [var "x"]) .=>. ((pApp "Mortal" [var "x"])))) .&.
                                                 ((for_all [V "x"] ((pApp "Socrates" [var "x"]) .=>. ((pApp "Human" [var "x"])))))) .=>.
                                                (((.~.) (for_all [V "x"] ((pApp "Socrates" [var "x"]) .=>. ((pApp "Mortal" [var "x"]))))))))
                    -- [~human(x) | mortal(x)], [~socrates(Sk1(x,y)) | human(Sk1(x,y))], socrates(Sk1(x,y)), ~mortal(Sk1(x,y))
                    -- ~1 | 2, ~3 | 4, 3, ~5?
                    , ClausalNormalForm [[((.~.) (pApp "Human" [x])), (pApp "Mortal" [x])],
                                         [((.~.) (pApp "Socrates" [fApp (toSkolem 1) [x,y]])), (pApp "Human" [fApp (toSkolem 1) [x,y]])],
                                         [(pApp "Socrates" [fApp (toSkolem 1) [x,y]])], [((.~.) (pApp "Mortal" [fApp (toSkolem 1) [x,y]]))]]
                    , ClausalNormalForm [[((.~.) (pApp "Human" [var "x2"])), (pApp "Mortal" [var "x2"])],
                                         [((.~.) (pApp "Socrates" [var "x2"])), (pApp "Human" [var "x2"])],
                                         [((.~.) (pApp "Socrates" [var "x"])), (pApp "Mortal" [var "x"])]] ]
       }
     ]
-}

chang43KB = 
    let e = fApp "e" []
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

chang43Conjecture :: forall formula term v p f. FirstOrderLogic formula term v p f => TestFormula formula
chang43Conjecture =
    let e = (fApp "e" [])
        (x, u, v, w) = (var "x", var "u", var "v", var "w") in
    withKB chang43KB $
    TestFormula { name = "G is commutative"
                , formula = for_all ["x"] (pApp "P" [x, x, e] .=>. (for_all ["u", "v", "w"] (pApp "P" [u, v, w] .=>. pApp "P" [v, u, w]))) 
                , expected =
                    [ FirstOrderFormula 
                      ((.~.) (((for_all ["x","y"] (exists ["z"] (pApp "P" [var ("x"),var ("y"),var ("z")]))) .&. ((((for_all ["x","y","z","u","v","w"] ((((pApp "P" [var ("x"),var ("y"),var ("u")]) .&. ((pApp "P" [var ("y"),var ("z"),var ("v")]))) .&. ((pApp "P" [var ("u"),var ("z"),var ("w")]))) .=>. ((pApp "P" [var ("x"),var ("v"),var ("w")])))) .&. ((for_all ["x","y","z","u","v","w"] ((((pApp "P" [var ("x"),var ("y"),var ("u")]) .&. ((pApp "P" [var ("y"),var ("z"),var ("v")]))) .&. ((pApp "P" [var ("x"),var ("v"),var ("w")]))) .=>. ((pApp "P" [var ("u"),var ("z"),var ("w")])))))) .&. ((((for_all ["x"] (pApp "P" [var ("x"),fApp ("e") [],var ("x")])) .&. ((for_all ["x"] (pApp "P" [fApp ("e") [],var ("x"),var ("x")])))) .&. (((for_all ["x"] (pApp "P" [var ("x"),fApp ("i") [var ("x")],fApp ("e") []])) .&. ((for_all ["x"] (pApp "P" [fApp ("i") [var ("x")],var ("x"),fApp ("e") []])))))))))) .=>. ((for_all ["x"] ((pApp "P" [var ("x"),var ("x"),fApp ("e") []]) .=>. ((for_all ["u","v","w"] ((pApp "P" [var ("u"),var ("v"),var ("w")]) .=>. ((pApp "P" [var ("v"),var ("u"),var ("w")]))))))))))
                      -- (∀x ∀y ∃z P(x,y,z)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(u,z,w) | P(x,v,w)) &
                      -- (∀x∀y∀z∀u∀v∀w ~P(x,y,u) | ~P(y,z,v) | ~P(x,v,w) | P(u,z,w)) &
                      -- (∀x P(x,e,x)) &
                      -- (∀x P(e,x,x)) &
                      -- (∀x P(x,i[x],e)) &
                      -- (∀x P(i[x],x,e)) &
                      -- (∃x P(x,x,e) & (∃u∃v∃w P(u,v,w) & ~P(v,u,w)))
                    , NegationNormalForm
                      (((for_all ["x","y"]
                         (exists ["z"]
                          (pApp "P" [var ("x"),var ("y"),var ("z")]))) .&.
                        ((((for_all ["x2","y2","z2","u","v","w"]
                            (((((.~.) (pApp "P" [var ("x2"),var ("y2"),var ("u")])) .|.
                               (((.~.) (pApp "P" [var ("y2"),var ("z2"),var ("v")])))) .|.
                              (((.~.) (pApp "P" [var ("u"),var ("z2"),var ("w")])))) .|.
                             ((pApp "P" [var ("x2"),var ("v"),var ("w")])))) .&.
                           ((for_all ["x3","y3","z3","u2","v2","w2"]
                             (((((.~.) (pApp "P" [var ("x3"),var ("y3"),var ("u2")])) .|.
                                (((.~.) (pApp "P" [var ("y3"),var ("z3"),var ("v2")])))) .|.
                               (((.~.) (pApp "P" [var ("x3"),var ("v2"),var ("w2")])))) .|.
                              ((pApp "P" [var ("u2"),var ("z3"),var ("w2")])))))) .&.
                          ((((for_all ["x4"]
                              (pApp "P" [var ("x4"),fApp ("e") [],var ("x4")])) .&.
                             ((for_all ["x5"]
                               (pApp "P" [fApp ("e") [],var ("x5"),var ("x5")])))) .&.
                            (((for_all ["x6"]
                               (pApp "P" [var ("x6"),fApp ("i") [var ("x6")],fApp ("e") []])) .&.
                              ((for_all ["x7"]
                                (pApp "P" [fApp ("i") [var ("x7")],var ("x7"),fApp ("e") []])))))))))) .&.
                       ((exists ["x8"]
                         ((pApp "P" [var ("x8"),var ("x8"),fApp ("e") []]) .&.
                          ((exists ["u3","v3","w3"]
                            ((pApp "P" [var ("u3"),var ("v3"),var ("w3")]) .&.
                             (((.~.) (pApp "P" [var ("v3"),var ("u3"),var ("w3")]))))))))))
                    , PrenexNormalForm
                      (for_all ["x"]
                       (for_all ["y"]
                        (exists ["z"]
                         (for_all ["x2"]
                          (for_all ["y2"]
                           (for_all ["z2"]
                            (for_all ["u"]
                             (for_all ["v"]
                              (for_all ["w"]
                               (for_all ["x3"]
                                (for_all ["y3"]
                                 (for_all ["z3"]
                                  (for_all ["u2"]
                                   (for_all ["v2"]
                                    (for_all ["w2"]
                                     (for_all ["x4"]
                                      (for_all ["x5"]
                                       (for_all ["x6"]
                                        (for_all ["x7"]
                                         (exists ["x8"]
                                          (exists ["u3"]
                                           (exists ["v3"]
                                            (exists ["w3"]
                                             (((pApp "P" [var ("x"),var ("y"),var ("z")]) .&.
                                               ((((((((.~.) (pApp "P" [var ("x2"),var ("y2"),var ("u")])) .|.
                                                     (((.~.) (pApp "P" [var ("y2"),var ("z2"),var ("v")])))) .|.
                                                    (((.~.) (pApp "P" [var ("u"),var ("z2"),var ("w")])))) .|.
                                                   ((pApp "P" [var ("x2"),var ("v"),var ("w")]))) .&.
                                                  ((((((.~.) (pApp "P" [var ("x3"),var ("y3"),var ("u2")])) .|.
                                                      (((.~.) (pApp "P" [var ("y3"),var ("z3"),var ("v2")])))) .|.
                                                     (((.~.) (pApp "P" [var ("x3"),var ("v2"),var ("w2")])))) .|.
                                                    ((pApp "P" [var ("u2"),var ("z3"),var ("w2")]))))) .&.
                                                 ((((pApp "P" [var ("x4"),fApp ("e") [],var ("x4")]) .&.
                                                    ((pApp "P" [fApp ("e") [],var ("x5"),var ("x5")]))) .&.
                                                   (((pApp "P" [var ("x6"),fApp ("i") [var ("x6")],fApp ("e") []]) .&.
                                                     ((pApp "P" [fApp ("i") [var ("x7")],var ("x7"),fApp ("e") []]))))))))) .&.
                                              (((pApp "P" [var ("x8"),var ("x8"),fApp ("e") []]) .&.
                                                (((pApp "P" [var ("u3"),var ("v3"),var ("w3")]) .&.
                                                  (((.~.) (pApp "P" [var ("v3"),var ("u3"),var ("w3")])))))))))))))))))))))))))))))))
                    , SkolemNormalForm
                      (for_all ["x"] (for_all ["y"] (for_all ["x2"] (for_all ["y2"] (for_all ["z2"] (for_all ["u"] (for_all ["v"] (for_all ["w"] (for_all ["x3"] (for_all ["y3"] (for_all ["z3"] (for_all ["u2"] (for_all ["v2"] (for_all ["w2"] (for_all ["x4"] (for_all ["x5"] (for_all ["x6"] (for_all ["x7"] (((pApp "P" [var ("x"),var ("y"),fApp (toSkolem 1) [var ("x"),var ("y")]]) .&. ((((((((.~.) (pApp "P" [var ("x2"),var ("y2"),var ("u")])) .|. (((.~.) (pApp "P" [var ("y2"),var ("z2"),var ("v")])))) .|. (((.~.) (pApp "P" [var ("u"),var ("z2"),var ("w")])))) .|. ((pApp "P" [var ("x2"),var ("v"),var ("w")]))) .&. ((((((.~.) (pApp "P" [var ("x3"),var ("y3"),var ("u2")])) .|. (((.~.) (pApp "P" [var ("y3"),var ("z3"),var ("v2")])))) .|. (((.~.) (pApp "P" [var ("x3"),var ("v2"),var ("w2")])))) .|. ((pApp "P" [var ("u2"),var ("z3"),var ("w2")]))))) .&. ((((pApp "P" [var ("x4"),fApp ("e") [],var ("x4")]) .&. ((pApp "P" [fApp ("e") [],var ("x5"),var ("x5")]))) .&. (((pApp "P" [var ("x6"),fApp ("i") [var ("x6")],fApp ("e") []]) .&. ((pApp "P" [fApp ("i") [var ("x7")],var ("x7"),fApp ("e") []]))))))))) .&. (((pApp "P" [fApp (toSkolem 2) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp (toSkolem 2) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp ("e") []]) .&. (((pApp "P" [fApp (toSkolem 3) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp (toSkolem 4) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp (toSkolem 5) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")]]) .&. (((.~.) (pApp "P" [fApp (toSkolem 4) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp (toSkolem 3) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],fApp (toSkolem 5) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")]]))))))))))))))))))))))))))
                    , SkolemNumbers (S.fromList [1,2,3,4,5])
                    -- From our algorithm

                    , let a = fApp (toSkolem 3) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")]
                          b = fApp (toSkolem 4) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")]
                          c = fApp (toSkolem 5) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")]
                      in 
                      ClausalNormalForm
                      [[(pApp "P" [var ("x"),var ("y"),fApp (toSkolem 1) [var ("x"),var ("y")]])],
                       [((.~.) (pApp "P" [var ("x2"),var ("y2"),var ("u")])),
                        ((.~.) (pApp "P" [var ("y2"),var ("z2"),var ("v")])),
                        ((.~.) (pApp "P" [var ("u"),var ("z2"),var ("w")])),
                        (pApp "P" [var ("x2"),var ("v"),var ("w")])],
                       [((.~.) (pApp "P" [var ("x3"),var ("y3"),var ("u2")])),
                        ((.~.) (pApp "P" [var ("y3"),var ("z3"),var ("v2")])),
                        ((.~.) (pApp "P" [var ("x3"),var ("v2"),var ("w2")])),
                        (pApp "P" [var ("u2"),var ("z3"),var ("w2")])],
                       [(pApp "P" [var ("x4"),fApp ("e") [],var ("x4")])],
                       [(pApp "P" [fApp ("e") [],var ("x5"),var ("x5")])],
                       [(pApp "P" [var ("x6"),fApp ("i") [var ("x6")],fApp ("e") []])],
                       [(pApp "P" [fApp ("i") [var ("x7")],var ("x7"),fApp ("e") []])],
                       [(pApp "P" [fApp (toSkolem 2) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],
                                        fApp (toSkolem 2) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x3"),var ("y3"),var ("z3"),var ("u2"),var ("v2"),var ("w2"),var ("x4"),var ("x5"),var ("x6"),var ("x7")],
                                        fApp ("e") []])],
                       [(pApp "P" [a, b, c])],
                       [((.~.) (pApp "P" [b, a, c]))]]

                    -- From the book
{-
                    , let (a, b, c) = 
                              (fApp (toSkolem 3) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x2"),var ("y2"),var ("z2"),var ("u2"),var ("v2"),var ("w2"),var ("x3"),var ("x3"),var ("x3"),var ("x3")],
                               fApp (toSkolem 4) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x2"),var ("y2"),var ("z2"),var ("u2"),var ("v2"),var ("w2"),var ("x3"),var ("x3"),var ("x3"),var ("x3")],
                               fApp (toSkolem 5) [var ("x"),var ("y"),var ("x2"),var ("y2"),var ("z2"),var ("u"),var ("v"),var ("w"),var ("x2"),var ("y2"),var ("z2"),var ("u2"),var ("v2"),var ("w2"),var ("x3"),var ("x3"),var ("x3"),var ("x3")]) in
                      ClausalNormalForm
                      [[(pApp "P" [var "x",var "y",fApp (toSkolem 1) [var "x",var "y"]])],
                       [((.~.) (pApp "P" [var "x",var "y",var "u"])),
                        ((.~.) (pApp "P" [var "y",var "z",var "v"])),
                        ((.~.) (pApp "P" [var "u",var "z",var "w"])),
                        (pApp "P" [var "x",var "v",var "w"])],
                       [((.~.) (pApp "P" [var "x",var "y",var "u"])),
                        ((.~.) (pApp "P" [var "y",var "z",var "v"])),
                        ((.~.) (pApp "P" [var "x",var "v",var "w"])),
                        (pApp "P" [var "u",var "z",var "w"])],
                       [(pApp "P" [var "x",fApp "e" [],var "x"])],
                       [(pApp "P" [fApp "e" [],var "x",var "x"])],
                       [(pApp "P" [var "x",fApp "i" [var "x"],fApp "e" []])],
                       [(pApp "P" [fApp "i" [var "x"],var "x",fApp "e" []])],
                       [(pApp "P" [var "x",
                                   var "x",
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
> :m +Logic.NormalForm
> let f = (.~.) (conj (map formula (snd chang43KB)) .=>. formula chang43Conjecture)
> putStrLn (runNormal (cnfTrace f))
-}

chang43ConjectureRenamed :: forall formula term v p f. FirstOrderLogic formula term v p f => TestFormula formula
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
                      ((.~.) ((((((((for_all ["x","y"] (exists ["z"] (pApp "P" [var "x",var "y",var "z"]))) .&.
                                    ((for_all ["x2","y2","z2","u","v","w"] ((((pApp "P" [var "x2",var "y2",var "u"]) .&.
                                                                                          ((pApp "P" [var "y2",var "z2",var "v"]))) .&.
                                                                                         ((pApp "P" [var "u",var "z2",var "w"]))) .=>.
                                                                                        ((pApp "P" [var "x2",var "v",var "w"])))))) .&.
                                   ((for_all ["x3","y3","z3","u2","v2","w2"] ((((pApp "P" [var "x3",var "y3",var "u2"]) .&.
                                                                                            ((pApp "P" [var "y3",var "z3",var "v2"]))) .&.
                                                                                           ((pApp "P" [var "x3",var "v2",var "w2"]))) .=>.
                                                                                          ((pApp "P" [var "u2",var "z3",var "w2"])))))) .&.
                                  ((for_all ["x4"] (pApp "P" [var "x4",fApp "e" [],var "x4"])))) .&.
                                 ((for_all ["x5"] (pApp "P" [fApp "e" [],var "x5",var "x5"])))) .&.
                                ((for_all ["x6"] (pApp "P" [var "x6",fApp "i" [var "x6"],fApp "e" []])))) .&.
                               ((for_all ["x7"] (pApp "P" [fApp "i" [var "x7"],var "x7",fApp "e" []])))) .=>.
                              ((for_all ["x8"] ((pApp "P" [var "x8",var "x8",fApp "e" []]) .=>.
                                                  ((for_all ["u3","v3","w3"] ((pApp "P" [var "u3",var "v3",var "w3"]) .=>.
                                                                                    ((pApp "P" [var "v3",var "u3",var "w3"]))))))))))
                    , let a = fApp (toSkolem 3) [var "x",var "y",var "x2",var "y2",var "z2",var "u",var "v",var "w",var "x3",var "y3",var "z3",var "u2",var "v2",var "w2",var "x4",var "x5",var "x6",var "x7"]
                          b = fApp (toSkolem 4) [var "x",var "y",var "x2",var "y2",var "z2",var "u",var "v",var "w",var "x3",var "y3",var "z3",var "u2",var "v2",var "w2",var "x4",var "x5",var "x6",var "x7"]
                          c = fApp (toSkolem 5) [var "x",var "y",var "x2",var "y2",var "z2",var "u",var "v",var "w",var "x3",var "y3",var "z3",var "u2",var "v2",var "w2",var "x4",var "x5",var "x6",var "x7"]
                          x' = fApp (toSkolem 2) [var "x",var "y",var "x2",var "y2",var "z2",var "u",var "v",var "w",var "x3",var "y3",var "z3",var "u2",var "v2",var "w2",var "x4",var "x5",var "x6",var "x7"] in 
                      ClausalNormalForm
                      [[(pApp "P" [var "x",var "y",fApp (toSkolem 1) [var "x",var "y"]])],
                       [((.~.) (pApp "P" [var "x2",var "y2",var "u"])),
                        ((.~.) (pApp "P" [var "y2",var "z2",var "v"])),
                        ((.~.) (pApp "P" [var "u",var "z2",var "w"])),
                        (pApp "P" [var "x2",var "v",var "w"])],
                       [((.~.) (pApp "P" [var "x3",var "y3",var "u2"])),
                        ((.~.) (pApp "P" [var "y3",var "z3",var "v2"])),
                        ((.~.) (pApp "P" [var "x3",var "v2",var "w2"])),
                        (pApp "P" [var "u2",var "z3",var "w2"])],
                       [(pApp "P" [var "x4",fApp "e" [],var "x4"])],
                       [(pApp "P" [fApp "e" [],var "x5",var "x5"])],
                       [(pApp "P" [var "x6",fApp "i" [var "x6"],fApp "e" []])],
                       [(pApp "P" [fApp "i" [var "x7"],var "x7",fApp "e" []])],
                       [(pApp "P" [x', x', fApp "e" []])],
                       [(pApp "P" [a, b, c])],
                       [((.~.) (pApp "P" [b, a, c]))]]                      
                    ]
                }

withKB :: forall formula term v p f. FirstOrderLogic formula term v p f =>
          (String, [TestFormula formula]) -> TestFormula formula -> TestFormula formula
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

kbKnowledge :: forall formula term v p f. FirstOrderLogic formula term v p f => (String, [TestFormula formula]) -> (String, [formula])
kbKnowledge kb = (fst (kb :: (String, [TestFormula formula])), map formula (snd kb))

proofs :: forall inf formula term v p f. (FirstOrderLogic formula term v p f, Implicative inf formula) =>
          [TestProof inf formula term v]
proofs =
    let -- dog = pApp "Dog" :: [term] -> formula
        -- cat = pApp "Cat" :: [term] -> formula
        -- owns = pApp "Owns" :: [term] -> formula
        kills = pApp "Kills" :: [term] -> formula
        -- animal = pApp "Animal" :: [term] -> formula
        -- animalLover = pApp "AnimalLover" :: [term] -> formula
        socrates = pApp "Socrates" :: [term] -> formula
        -- human = pApp "Human" :: [term] -> formula
        mortal = pApp "Mortal" :: [term] -> formula

        jack :: term
        jack = fApp "Jack" []
        tuna :: term
        tuna = fApp "Tuna" []
        curiosity :: term
        curiosity = fApp "Curiosity" [] in

    [ TestProof
      { proofName = "jack kills tuna"
      , proofKnowledge = kbKnowledge animalKB
      , conjecture = kills [jack, tuna]
      , proofExpected = 
          [ ChiouKB [WithId {wiItem = makeINF (S.fromList []) (S.fromList [(pApp "Dog" [fApp (toSkolem 1) []])]), wiIdent = 1},
                     WithId {wiItem = makeINF (S.fromList []) (S.fromList [(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])]), wiIdent = 1},
                     WithId {wiItem = makeINF (S.fromList [(pApp "Dog" [var "y"]),(pApp "Owns" [var "x",var "y"])]) (S.fromList [(pApp "AnimalLover" [var "x"])]), wiIdent = 2},
                     WithId {wiItem = makeINF (S.fromList [(pApp "Animal" [var "y"]),(pApp "AnimalLover" [var "x"]),(pApp "Kills" [var "x",var "y"])]) (S.fromList []), wiIdent = 3},
                     WithId {wiItem = makeINF (S.fromList []) (S.fromList [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]),(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])]), wiIdent = 4},
                     WithId {wiItem = makeINF (S.fromList []) (S.fromList [(pApp "Cat" [fApp "Tuna" []])]), wiIdent = 5},
                     WithId {wiItem = makeINF (S.fromList [(pApp "Cat" [var "x"])]) (S.fromList [(pApp "Animal" [var "x"])]), wiIdent = 6}]
          , ChiouResult (False,
                         [(inf' [(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])] [],fromList []),
                          (inf' [] [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []])],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "AnimalLover" [fApp "Curiosity" []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Curiosity" [],var "y"])] [],fromList []),
                          (inf' [(pApp "AnimalLover" [fApp "Curiosity" []]),(pApp "Cat" [fApp "Tuna" []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Curiosity" [],var "y"])] [],fromList []),
                          (inf' [(pApp "AnimalLover" [fApp "Curiosity" []])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Curiosity" [],var "y"])] [],fromList []),
                          (inf' [(pApp "Owns" [fApp "Curiosity" [],fApp (toSkolem 1) []])] [],fromList [])])
          ]
      }
    , TestProof
      { proofName = "curiosity kills tuna"
      , proofKnowledge = kbKnowledge animalKB
      , conjecture = kills [curiosity, tuna]
      , proofExpected =
          [ ChiouKB [WithId {wiItem = inf' [] [(pApp "Dog" [fApp (toSkolem 1) []])], wiIdent = 1},
                     WithId {wiItem = inf' [] [(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])], wiIdent = 1},
                     WithId {wiItem = inf' [(pApp "Dog" [var "y"]),(pApp "Owns" [var "x",var "y"])] [(pApp "AnimalLover" [var "x"])], wiIdent = 2},
                     WithId {wiItem = inf' [(pApp "Animal" [var "y"]),(pApp "AnimalLover" [var "x"]),(pApp "Kills" [var "x",var "y"])] [], wiIdent = 3},
                     WithId {wiItem = inf' [] [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []]),(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])], wiIdent = 4},
                     WithId {wiItem = inf' [] [(pApp "Cat" [fApp "Tuna" []])], wiIdent = 5},
                     WithId {wiItem = inf' [(pApp "Cat" [var "x"])] [(pApp "Animal" [var "x"])], wiIdent = 6}]
          , ChiouResult (True,
                         [(inf' [(pApp "Kills" [fApp "Curiosity" [],fApp "Tuna" []])] [],fromList []),
                          (inf' [] [(pApp "Kills" [fApp "Jack" [],fApp "Tuna" []])],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "AnimalLover" [fApp "Jack" []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Jack" [],var "y"])] [],fromList []),
                          (inf' [(pApp "AnimalLover" [fApp "Jack" []]),(pApp "Cat" [fApp "Tuna" []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []]),(pApp "Dog" [fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Jack" [],var "y"])] [],fromList []),
                          (inf' [(pApp "AnimalLover" [fApp "Jack" []])] [],fromList []),
                          (inf' [(pApp "Animal" [fApp "Tuna" []])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []]),(pApp "Dog" [fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Dog" [var "y"]),(pApp "Owns" [fApp "Jack" [],var "y"])] [],fromList []),
                          (inf' [(pApp "Cat" [fApp "Tuna" []])] [],fromList []),
                          (inf' [(pApp "Owns" [fApp "Jack" [],fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [(pApp "Dog" [fApp (toSkolem 1) []])] [],fromList []),
                          (inf' [] [],fromList [])])
          ]
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
      , proofKnowledge = kbKnowledge socratesKB
      , conjecture = for_all ["x"] (socrates [x] .=>. mortal [x])
      , proofExpected = 
         [ ChiouKB [WithId {wiItem = inf' [(pApp "Human" [var "x"])] [(pApp "Mortal" [var "x"])], wiIdent = 1},
                    WithId {wiItem = inf' [(pApp "Socrates" [var "x"])] [(pApp "Human" [var "x"])], wiIdent = 2}]
         , ChiouResult (True,
                        [(inf' [] [(pApp "Socrates" [fApp (toSkolem 1) []])],fromList []),
                         (inf' [(pApp "Mortal" [fApp (toSkolem 1) []])] [],fromList []),
                         (inf' [] [(pApp "Human" [fApp (toSkolem 1) []])],fromList []),
                         (inf' [(pApp "Human" [fApp (toSkolem 1) []])] [],fromList []),
                         (inf' [] [(pApp "Mortal" [fApp (toSkolem 1) []])],fromList []),
                         (inf' [] [],fromList [])])]
      }
    , let x = var "x" in
      TestProof
      { proofName = "socrates is not mortal"
      , proofKnowledge = kbKnowledge socratesKB
      , conjecture = (.~.) (for_all ["x"] (socrates [x] .=>. mortal [x]))
      , proofExpected = 
         [ ChiouKB [WithId {wiItem = inf' [(pApp "Human" [var "x"])] [(pApp "Mortal" [var "x"])], wiIdent = 1},
                    WithId {wiItem = inf' [(pApp "Socrates" [var "x"])] [(pApp "Human" [var "x"])], wiIdent = 2}]
         , ChiouResult (False
                       ,[(inf' [(pApp "Socrates" [var "x"])] [(pApp "Mortal" [var "x"])],fromList [("x",var "x")])])]
      }
    , let x = var "x" in
      TestProof
      { proofName = "socrates exists and is is not mortal"
      , proofKnowledge = kbKnowledge socratesKB
      , conjecture = (.~.) (exists ["x"] (socrates [x]) .&. for_all ["x"] (socrates [x] .=>. mortal [x]))
      , proofExpected = 
         [ ChiouKB [WithId {wiItem = inf' [(pApp "Human" [var "x"])] [(pApp "Mortal" [var "x"])], wiIdent = 1},
                    WithId {wiItem = inf' [(pApp "Socrates" [var "x"])] [(pApp "Human" [var "x"])], wiIdent = 2}]
         , ChiouResult (False,
                        [(inf' [] [(pApp "Socrates" [fApp (toSkolem 1) []])],fromList []),
                         (inf' [(pApp "Socrates" [var "x2"])] [(pApp "Mortal" [var "x2"])],fromList [("x2",var "x2")]),
                         (inf' [] [(pApp "Human" [fApp (toSkolem 1) []])],fromList []),
                         (inf' [] [(pApp "Mortal" [fApp (toSkolem 1) []])],fromList [("x2",var "x2")])])]
      }
    ]

inf' :: Implicative inf formula => [formula] -> [formula] -> inf
inf' l1 l2 = makeINF (S.fromList l1) (S.fromList l2)
