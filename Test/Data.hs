{-# LANGUAGE DeriveDataTypeable, OverloadedStrings  #-}
{-# OPTIONS -fno-warn-name-shadowing -fno-warn-missing-signatures #-}
module Test.Data
    ( TestFormula(..)
    , Expected(..)
    , formulas
    , animalKB
    , animalConjectures
    ) where

import Logic.FirstOrder (FirstOrderLogic(..))
import Logic.Logic (Logic(..), Boolean(..))
import Test.Types

formulas :: [TestFormula]
formulas =
    [ let n = (.~.) :: Logic formula => formula -> formula
          p = pApp (Pr "p") :: [Term] -> Formula
          q = pApp (Pr "q") :: [Term] -> Formula
          r = pApp (Pr "r") :: [Term] -> Formula
          s = pApp (Pr "s") :: [Term] -> Formula
          t = pApp (Pr "t") :: [Term] -> Formula
          p0 = p []
          q0 = q []
          r0 = r []
          s0 = s []
          t0 = t [] in
      TestFormula
      { formula = p0 .|. q0 .&. r0 .|. n s0 .&. n t0
      , name = "operator precedence"
      , expected = [ FirstOrderFormula ((p0 .|. q0) .&. (r0 .|. (n s0)) .&. (n t0)) ] }
    ]

animalKB :: (String, [TestFormula])
animalKB =
    let x = var "x"
        y = var "y"
        dog = pApp "Dog" :: [Term] -> Formula
        cat = pApp "Cat" :: [Term] -> Formula
        owns = pApp "Owns" :: [Term] -> Formula
        kills = pApp "Kills" :: [Term] -> Formula
        animal = pApp "Animal" :: [Term] -> Formula
        animalLover = pApp "AnimalLover" :: [Term] -> Formula
        jack = fApp "Jack" [] :: Term
        tuna = fApp "Tuna" [] :: Term
        curiosity = fApp "Curiosity" [] :: Term in
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
       , expected = [ PrenexNormalForm (for_all [V "x"] (for_all [V "y"] ((((.~.) (pApp (Pr "Dog") [var (V "y")])) .|.
                                                                           (((.~.) (pApp (Pr "Owns") [var (V "x"),var (V "y")])))) .|.
                                                                          ((pApp (Pr "AnimalLover") [var (V "x")])))))
                    , ClausalNormalForm [[((.~.) (pApp (Pr "Dog") [var (V "y")])),((.~.) (pApp (Pr "Owns") [var (V "x"),var (V "y")])),(pApp (Pr "AnimalLover") [var (V "x")])]] ]
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
    let kills = pApp "Kills" :: [Term] -> Formula
        jack = fApp "Jack" [] :: Term
        tuna = fApp "Tuna" [] :: Term
        curiosity = fApp "Curiosity" [] :: Term in

    map (withKB animalKB) $
     [ TestFormula
       { formula = (.~.) (kills [jack, tuna]) -- [[Neg 5]]            -- Inconsistant
       , name = "not (jack kills tuna)"
       , expected =
           [ ClausalNormalForm  [[(.~.) (pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []])]]
           , SatResult True ]
       -- negated_conjecture: ~kills(jack,tuna)
       }
     , TestFormula
       { formula = (.~.) (kills [curiosity, tuna])        -- Theorem
       , name = "not (curiosity kills tuna)"
       , expected =
           [ ClausalNormalForm  [[(.~.) (pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])]]
           , SatResult False ]
       -- negated_conjecture: ~kills(curiosity,tuna)
       }
     ]

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
