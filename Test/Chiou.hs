{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             RankNTypes, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-orphans -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module Test.Chiou (tests, V(..), AtomicFunction(..)) where

import Control.Monad.Identity (runIdentity)
import Data.String (IsString(..))
import Logic.Chiou.FirstOrderLogic (Sentence(..), Term(..), Quantifier(..), Connective(..))
import Logic.Chiou.KnowledgeBase (loadKB, theoremKB, validKB)
import Logic.Chiou.Monad (runProverT)
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..), fromINF)
import Logic.Instances.Chiou ()
import qualified Logic.Instances.Parameterized as P
import Logic.Logic (Logic(..))
import Logic.Predicate (Skolem(..), PredicateLogic(..), convertPred, showForm)
import Test.HUnit

-- | Variable names
newtype V = V String
    deriving (Eq,Ord) -- ,Data,Typeable,Read,Monoid,IsString

instance IsString V where
    fromString = V

data AtomicFunction
    = AtomicFunction String
    | SkolemFunction Int
    deriving (Show, Eq, Ord)

instance Skolem AtomicFunction where
    toSkolem = SkolemFunction
    fromSkolem (SkolemFunction n) = Just n
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString  = AtomicFunction

type SentenceVPA = Sentence V Pr AtomicFunction
type FormulaPF = P.Formula V Pr AtomicFunction

-- |Argument to conversion tests.  These pairs look the same, but
-- they use the class methods to construct different types, as
-- you can see from the signature.
testFormulas ::[(String, SentenceVPA, FormulaPF)]
testFormulas =
    [ ( "exists, equal"
      , exists [fromString "x"] (x .=. y)
      , exists [fromString "x"] (x .=. y))
    , ( "fApp"
      , (s [fApp (fromString "a") [x, y]])
      , (s [fApp (fromString "a") [x, y]]))
    , ( "forall, imply, and, var, pApp"
     , for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
     , for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x])))]
    where

x :: (PredicateLogic formula term v p f, IsString v) => term
x = var (fromString "x")
y :: (PredicateLogic formula term v p f, IsString v) => term
y = var (fromString "y")

s :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
s = pApp (fromString "s")
m :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
m = pApp (fromString "m")
h :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
h = pApp (fromString "h")

pairTest :: (String, SentenceVPA, FormulaPF) -> [Test]
pairTest (s, f1, f2) =
    [ TestCase (assertEqual (s ++ ", Chiou to FormulaPF") f1 (convertPred id id id f2)),
      TestCase (assertEqual (s ++ ", FormulaPF to Chiou") f2 (convertPred id id id f1)) ]

tests :: [Test]
tests = concatMap pairTest testFormulas ++ testProver

-- |A newtype for the Primitive Predicate parameter.
newtype Pr = Pr String deriving (Eq)

instance IsString Pr where
    fromString = Pr

animalSentences :: [SentenceVPA]
animalSentences =
    [ exists ["x"] ((dog [x]) .&. (owns [jack, x]))
    , for_all ["x"] (((exists ["y"] (dog [y])) .&. (owns [x, y])) .=>. (animalLover [x]))
    , for_all ["x"] ((animalLover [x]) .=>. (for_all ["y"] ((animal [y]) .=>. ((.~.) (kills [x, y])))))
    , (kills [jack, tuna]) .|. (kills [curiosity, tuna])
    , cat [tuna]
    , for_all ["x"] ((cat [x]) .=>. (animal [x])) ]

expected3 =
    [(Quantifier ForAll [V "x"] (Connective (Predicate (Pr "Socrates") [Variable (V "x")]) Imply (Predicate (Pr "Human") [Variable (V "x")])),
      Just [INF [NFPredicate (Pr "Socrates") [Variable (V "x")]] [NFPredicate (Pr "Human") [Variable (V "x")]]]),
     (Quantifier ForAll [V "x"] (Connective (Predicate (Pr "Human") [Variable (V "x")]) Imply (Predicate (Pr "Mortal") [Variable (V "x")])),
      Just [INF [NFPredicate (Pr "Human") [Variable (V "x")]] [NFPredicate (Pr "Mortal") [Variable (V "x")]]]),(Connective (Predicate (Pr "Socrates") [Variable (V "x")]) Imply (Predicate (Pr "Mortal") [Variable (V "x")]),Just [INF [NFPredicate (Pr "Socrates") [Variable (V "x")]] [NFPredicate (Pr "Mortal") [Variable (V "x")]]]),
     (Quantifier Exists [V "x"] (Predicate (Pr "Socrates") [Variable (V "x")]),
      Just [INF [] [NFPredicate (Pr "Socrates") [Function (toSkolem 1) []]]])]
expected4 =
    ( Just False
    , [(INF []													[NFPredicate (Pr "Socrates") [Variable (V "x")]],	[(V "x",Variable (V "x"))]),
       (INF []													[NFPredicate (Pr "Mortal") [Variable (V "x")]],		[(V "x",Variable (V "x"))]),
       (INF []													[NFPredicate (Pr "Human") [Variable (V "x")]],		[(V "x",Variable (V "x"))])]
    , [(INF [NFPredicate (Pr "Socrates") [Variable (V "x")],NFPredicate (Pr "Mortal") [Variable (V "x")]]	[],							[(V "x",Variable (V "x"))]),
       (INF [NFPredicate (Pr "Human") [Variable (V "x")],NFPredicate (Pr "Socrates") [Variable (V "x")]]	[],							[(V "x",Variable (V "x"))]),
       (INF [NFPredicate (Pr "Mortal") [Function (toSkolem 1) []]]					[],							[(V "x",Function (toSkolem 1) [])]),
       (INF [NFPredicate (Pr "Socrates") [Variable (V "x")],NFPredicate (Pr "Socrates") [Variable (V "x")]]	[],							[(V "x",Variable (V "x"))]),
       (INF [NFPredicate (Pr "Human") [Function (toSkolem 1) []]]					[],							[(V "x",Function (toSkolem 1) [])]),
       (INF [NFPredicate (Pr "Socrates") [Function (toSkolem 1) []]]					[],							[(V "x",Function (toSkolem 1) [])]),
       (INF []													[],							[(V "x",Function (toSkolem 1) [])])])
expected5 =
    (Just False,
     [(Connective (Predicate (Pr "Socrates") [Variable (V "x")]) Imply (Predicate (Pr "False") []),[(V "x",Variable (V "x"))])],
     [(Connective (Predicate (Pr "True") []) Imply (Predicate (Pr "Socrates") [Function (SkolemFunction 1) []]),[]),
      (Connective (Predicate (Pr "True") []) Imply (Predicate (Pr "Human") [Function (SkolemFunction 1) []]),[]),
      (Connective (Predicate (Pr "Mortal") [Function (SkolemFunction 1) []]) Imply (Predicate (Pr "False") []),[]),
      (Connective (Predicate (Pr "True") []) Imply (Predicate (Pr "Mortal") [Function (SkolemFunction 1) []]),[]),
      (Connective (Predicate (Pr "Human") [Function (SkolemFunction 1) []]) Imply (Predicate (Pr "False") []),[]),
      (Connective (Predicate (Pr "True") []) Imply (Predicate (Pr "False") []),[])])

dog = pApp "Dog"
cat = pApp "Cat"
owns = pApp "Owns"
kills = pApp "Kills"
animal = pApp "Animal"
animalLover = pApp "AnimalLover"
socrates = pApp "Socrates"
human = pApp "Human"
mortal = pApp "Mortal"

jack :: Term V AtomicFunction
jack = fApp (fromString "Jack") []
tuna :: Term V AtomicFunction
tuna = fApp (fromString "Tuna") []
curiosity :: Term V AtomicFunction
curiosity = fApp (fromString "Curiosity") []

testProver :: [Test]
testProver =
    [ TestCase (assertEqual "prover test 1"
                            (False,
                             [(INF [NFPredicate (Pr "Kills") [Function (AtomicFunction "Jack") [],Function (AtomicFunction "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (AtomicFunction "Curiosity") [],Function (AtomicFunction "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Function (toSkolem 1) []],NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Function (toSkolem 1) []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Function (toSkolem 1) []],NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Curiosity") [],Function (toSkolem 1) []]] [],[])])
                            (runIdentity (runProverT (loadKB animalSentences >>
                                                      theoremKB (kills [jack, tuna])))))
    , TestCase (assertEqual "prover test 2"
                           (True,
                            [(INF [NFPredicate (Pr "Kills") [Function (AtomicFunction "Curiosity") [],Function (AtomicFunction "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (AtomicFunction "Jack") [],Function (AtomicFunction "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Jack") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Jack") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Function (toSkolem 1) []],NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Function (toSkolem 1) []],NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (AtomicFunction "Jack") []]] [],[]),(INF [NFPredicate (Pr "Animal") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Function (toSkolem 1) []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []],NFPredicate (Pr "Dog") [Function (toSkolem 1) []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Function (toSkolem 1) []],NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Function (toSkolem 1) []],NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (AtomicFunction "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (AtomicFunction "Jack") [],Function (toSkolem 1) []]] [],[]),(INF [NFPredicate (Pr "Dog") [Function (toSkolem 1) []]] [],[]),(INF [] [],[])])
                           (runIdentity (runProverT (loadKB animalSentences >>
                                                     theoremKB (kills [curiosity, tuna])))))
    , TestCase (assertEqual "prover test 3: socrates is mortal"
                            expected3
                            (testLoad [ for_all ["x"] (socrates [x] .=>. human [x]) -- Socrates exists and is mortal
                                      , for_all ["x"] (human [x] .=>. mortal [x])
                                      , socrates [x] .=>. mortal [x]
                                      , exists ["x"] (socrates [x]) ]))
    , TestCase (assertEqual "prover test 4: socrates is not mortal"
                            expected4
                            (runIdentity 
                             (runProverT
                              (loadKB [ for_all ["x"] (socrates [x] .=>. human [x]) -- Socrates exists and is not mortal
                                      , for_all ["x"] (human [x] .=>. mortal [x])
                                      , exists ["x"] (socrates [x]) ] >>
                               validKB (socrates [x] .=>. (.~.) (mortal [x]))))))
    , TestCase (assertEqual "prover test 5: socrates exists is not mortal"
                            expected5
                            (testSentence
                             [ for_all ["x"] (socrates [x] .=>. human [x]) -- Socrates is not mortal and exists
                             , for_all ["x"] (human [x] .=>. mortal [x])
                             , for_all ["x"] (socrates [x] .=>. (.~.) (mortal [x])) ]
                             (exists ["x"] (socrates [x]))))
    ]
    where
      kills = pApp "Kills"
      jack = fApp "Jack" []
      curiosity = fApp "Curiosity" []
      tuna = fApp "Tuna" []

testLoad kb = runIdentity (runProverT (loadKB kb))

testSentence kb s = 
    f (runIdentity (runProverT (loadKB kb >> validKB s)))
    where
      f (flag, xs, ys) = (flag, map fromUnify xs, map fromUnify ys)
      fromUnify (inf, subst) = (fromINF inf, subst)
{-
    map (\ (flag, xs, ys) ->
             (flag,
              map fromUnify xs,
              map fromUnify ys)) 

              map (\ (inf, prs) -> (fromINF inf, prs)) xs,
              map (\ (inf, prs) -> (fromINF inf, prs)) ys
-}
-- Ugly Printing

deriving instance (Show v, Show p, Show f) => Show (Sentence v p f)
deriving instance (Show v, Show p, Show f) => Show (ImplicativeNormalForm v p f)
deriving instance (Show v, Show p, Show f) => Show (NormalSentence v p f)
deriving instance (Show v, Show f) => Show (Term v f)
deriving instance Show Quantifier
deriving instance Show Connective

deriving instance Show V
deriving instance Show Pr
deriving instance Show FormulaPF
