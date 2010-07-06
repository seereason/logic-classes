{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-orphans #-}
module Test.Chiou (tests) where

import Chiou.FirstOrderLogic
import Data.String (IsString(..))
import qualified Logic.Instances.Parameterized as P
import Logic.Instances.Chiou (AtomicFunction(..))
import Logic.Logic (Logic(..))
import Logic.Predicate (PredicateLogic(..), convertPred, showForm {-, toPropositional, InfixPred(..), freeVars, substitute-})
import Test.HUnit

instance Show (P.Formula String String) where
    show = showForm

type FormulaPF = P.Formula String String

-- |Argument to conversion tests.  These pairs look the same, but
-- they use the class methods to construct different types, as
-- you can see from the signature.
testFormulas ::[(String, Sentence, FormulaPF)]
testFormulas =
    [ ( "exists, equal"
      , exists ["x"] (x .=. y)
      , exists ["x"] (x .=. y))
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
    [ TestCase (assertEqual (s ++ ", Chiou to FormulaPF") f1 (convertPred vc pc AtomicFunction f2)),
      TestCase (assertEqual (s ++ ", FormulaPF to Chiou") f2 (convertPred P.V pc fc f1)) ]

tests :: [Test]
tests = concatMap pairTest testFormulas

vc :: P.V -> String
vc (P.V s) = s

pc :: String -> String
pc = id

fc :: AtomicFunction -> String
fc (AtomicFunction s) = s
fc (AtomicSkolemFunction n) = show n
