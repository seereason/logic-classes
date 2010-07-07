{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             RankNTypes, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-orphans -fno-warn-missing-signatures #-}
module Test.Chiou (tests, V(..)) where

import qualified Chiou.FirstOrderLogic as C
import Chiou.FirstOrderLogic (Term(..))
import Chiou.KnowledgeBase (loadKB, theoremKB, validKB)
import Chiou.Monad (runProverT)
import qualified Chiou.NormalForm as C
import Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..))
import Control.Monad.Identity (runIdentity)
import Data.String (IsString(..))
import qualified Logic.Instances.Parameterized as P
import Logic.Instances.Chiou (AtomicFunction(..))
import Logic.Logic (Logic(..))
import Logic.Predicate (PredicateLogic(..), convertPred {-, showForm-})
import Test.HUnit

-- | Variable names
newtype V = V String
    deriving (Eq,Ord) -- ,Data,Typeable,Read,Monoid,IsString

instance IsString V where
    fromString = V

type Sentence = C.Sentence V Pr AtomicFunction
type FormulaPF = P.Formula V Pr String

-- |Argument to conversion tests.  These pairs look the same, but
-- they use the class methods to construct different types, as
-- you can see from the signature.
testFormulas ::[(String, Sentence, FormulaPF)]
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

pairTest :: (String, Sentence, FormulaPF) -> [Test]
pairTest (s, f1, f2) =
    [ TestCase (assertEqual (s ++ ", Chiou to FormulaPF") f1 (convertPred id pc AtomicFunction f2)),
      TestCase (assertEqual (s ++ ", FormulaPF to Chiou") f2 (convertPred id pc fc f1)) ]

tests :: [Test]
tests = concatMap pairTest testFormulas ++ testProver

pc :: Pr -> Pr
pc = id

fc :: AtomicFunction -> String
fc (AtomicFunction s) = s
fc (AtomicSkolemFunction n) = show n

-- |A newtype for the Primitive Predicate parameter.
newtype Pr = Pr String deriving (Eq)

instance IsString Pr where
    fromString = Pr

animalSentences :: [Sentence]
animalSentences =
    [ exists ["x"] ((dog [x]) .&. (owns [jack, x]))
    , for_all ["x"] (((exists ["y"] (dog [y])) .&. (owns [x, y])) .=>. (animalLover [x]))
    , for_all ["x"] ((animalLover [x]) .=>. (for_all ["y"] ((animal [y]) .=>. ((.~.) (kills [x, y])))))
    , (kills [jack, tuna]) .|. (kills [curiosity, tuna])
    , cat [tuna]
    , for_all ["x"] ((cat [x]) .=>. (animal [x])) ]

socratesSentences1 :: [Sentence]
socratesSentences1 =
    [ for_all ["x"] (socrates [x] .=>. human [x])
    , for_all ["x"] (human [x] .=>. mortal [x]) ]

socratesSentences2 :: [Sentence]
socratesSentences2 = [ for_all ["x"] (socrates [x] .=>. (.~.) (mortal [x])),
                       exists ["x"] (socrates [x]) ] ++ socratesSentences1

socratesSentences3 :: [Sentence]
socratesSentences3 = [ exists ["x"] (socrates [x]) ] ++ socratesSentences1

dog = pApp "Dog"
cat = pApp "Cat"
owns = pApp "Owns"
kills = pApp "Kills"
animal = pApp "Animal"
animalLover = pApp "AnimalLover"
socrates = pApp "Socrates"
human = pApp "Human"
mortal = pApp "Mortal"

jack = fApp (fromString "Jack") []
tuna = fApp (fromString "Tuna") []
curiosity = fApp (fromString "Curiosity") []

testProver :: [Test]
testProver =
    [ TestCase (assertEqual "prover test 1"
                            (False,
                             [(INF [NFPredicate (Pr "Kills") [Constant (AtomicFunction "Jack"),Constant (AtomicFunction "Tuna")]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Constant (AtomicFunction "Curiosity"),Constant (AtomicFunction "Tuna")]],[]),(INF [NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Curiosity")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Variable (V "y")],NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Curiosity")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Variable (V "y")],NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Curiosity")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Constant (AtomicSkolemFunction 1)]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Curiosity"),Constant (AtomicSkolemFunction 1)]] [],[])])
                            (runIdentity (runProverT (loadKB animalSentences >>
                                                      theoremKB (kills [jack, tuna])))))
    , TestCase (assertEqual "prover test 2"
                           (True,
                            [(INF [NFPredicate (Pr "Kills") [Constant (AtomicFunction "Curiosity"),Constant (AtomicFunction "Tuna")]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Constant (AtomicFunction "Jack"),Constant (AtomicFunction "Tuna")]],[]),(INF [NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Jack")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Variable (V "y")],NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Jack")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Dog") [Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Variable (V "y")],NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Constant (AtomicFunction "Jack")]] [],[]),(INF [NFPredicate (Pr "Animal") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Constant (AtomicSkolemFunction 1)]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")],NFPredicate (Pr "Dog") [Constant (AtomicSkolemFunction 1)]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Constant (AtomicSkolemFunction 1)],NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y")],NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Constant (AtomicFunction "Tuna")]] [],[]),(INF [NFPredicate (Pr "Owns") [Constant (AtomicFunction "Jack"),Constant (AtomicSkolemFunction 1)]] [],[]),(INF [NFPredicate (Pr "Dog") [Constant (AtomicSkolemFunction 1)]] [],[]),(INF [] [],[])])
                           (runIdentity (runProverT (loadKB animalSentences >>
                                                     theoremKB (kills [curiosity, tuna])))))
    , TestCase (assertEqual "prover test 3: socrates is mortal"
                           (Just True,
                            [(INF [] [NFPredicate (Pr "Socrates") [Variable (V "x")]],[(V "x",Variable (V "x"))]),(INF [NFPredicate (Pr "Mortal") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [] [NFPredicate (Pr "Human") [Variable (V "x")]],[(V "x",Variable (V "x"))]),(INF [NFPredicate (Pr "Human") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [] [NFPredicate (Pr "Mortal") [Variable (V "x")]],[(V "x",Variable (V "x"))]),(INF [] [],[(V "x",Variable (V "x"))])],[(INF [NFPredicate (Pr "Socrates") [Variable (V "x")]] [NFPredicate (Pr "Mortal") [Variable (V "x")]],[(V "x",Variable (V "x"))])])
                           (testSentence socratesSentences1 (socrates [x] .=>. mortal [x])))
    , TestCase (assertEqual "prover test 4a: socrates exists and is not mortal"
                           (Nothing,
                            [(INF [NFPredicate (Pr "Socrates") [Variable (V "x")]] [NFPredicate (Pr "Mortal") [Variable (V "x")]],[(V "x",Variable (V "x"))]),(INF [] [NFPredicate (Pr "Mortal") [Constant (AtomicSkolemFunction 1)]],[(V "x",Constant (AtomicSkolemFunction 1))])],
                            [(INF [] [NFPredicate (Pr "Socrates") [SkolemConstant 1]],[]),(INF [NFPredicate (Pr "Mortal") [SkolemConstant 1]] [],[]),(INF [] [NFPredicate (Pr "Human") [SkolemConstant 1]],[]),(INF [NFPredicate (Pr "Human") [SkolemConstant 1]] [],[]),(INF [] [NFPredicate (Pr "Mortal") [SkolemConstant 1]],[]),(INF [NFPredicate (Pr "Socrates") [SkolemConstant 1]] [],[])])
                           (testSentence socratesSentences3 (exists ["x"] (socrates [x] .&. (.~.) (mortal [x])))))
    , TestCase (assertEqual "prover test 4b: socrates exists and is mortal"
                           (Just True,
                            [(INF [NFPredicate (Pr "Socrates") [Variable (V "x")],NFPredicate (Pr "Mortal") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [NFPredicate (Pr "Mortal") [Constant (AtomicSkolemFunction 1)]] [],[(V "x",Constant (AtomicSkolemFunction 1))]),(INF [NFPredicate (Pr "Human") [Variable (V "x")],NFPredicate (Pr "Socrates") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [NFPredicate (Pr "Human") [Constant (AtomicSkolemFunction 1)]] [],[(V "x",Constant (AtomicSkolemFunction 1))]),(INF [NFPredicate (Pr "Socrates") [Variable (V "x")],NFPredicate (Pr "Socrates") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [NFPredicate (Pr "Socrates") [Constant (AtomicSkolemFunction 1)]] [],[(V "x",Constant (AtomicSkolemFunction 1))]),(INF [] [],[(V "x",Constant (AtomicSkolemFunction 1))])],
                            [(INF [] [NFPredicate (Pr "Socrates") [SkolemConstant 1]],[]),(INF [] [NFPredicate (Pr "Mortal") [SkolemConstant 1]],[]),(INF [] [NFPredicate (Pr "Human") [SkolemConstant 1]],[]),(INF [] [NFPredicate (Pr "Mortal") [SkolemConstant 1]],[])])
                           (testSentence socratesSentences3 (exists ["x"] (socrates [x] .&. mortal [x]))))
    -- Why can't we show that s(x) => ~m(x) conflicts with s(x) => h(x) & h(x) => m(x)?
    , TestCase (assertEqual "prover test 5: socrates exists"
                           (Just True,
                            [(INF [NFPredicate (Pr "Socrates") [Variable (V "x")]] [],[(V "x",Variable (V "x"))]),(INF [] [],[(V "x",Constant (AtomicSkolemFunction 1))])],
                            [(INF [] [NFPredicate (Pr "Socrates") [SkolemConstant 1]],[]),(INF [NFPredicate (Pr "Mortal") [SkolemConstant 1]] [],[]),(INF [] [NFPredicate (Pr "Human") [SkolemConstant 1]],[])])
                           (testSentence socratesSentences2 (exists ["x"] (socrates [x]))))
    ]
    where
      kills = pApp "Kills"
      jack = fApp "Jack" []
      curiosity = fApp "Curiosity" []
      tuna = fApp "Tuna" []

testSentence kb s = runIdentity (runProverT (loadKB kb >> validKB s))

-- Ugly Printing

deriving instance (Show v, Show p, Show f) => Show (C.Sentence v p f)
deriving instance (Show v, Show p, Show f) => Show (C.ImplicativeNormalForm v p f)
deriving instance (Show v, Show p, Show f) => Show (C.NormalSentence v p f)
deriving instance (Show v, Show f) => Show (C.Term v f)
deriving instance Show C.Quantifier
deriving instance Show C.Connective

deriving instance Show V
deriving instance Show Pr
deriving instance Show FormulaPF
