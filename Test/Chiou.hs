{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-missing-signatures -fno-warn-orphans #-}
module Test.Chiou (tests) where

import Chiou.FirstOrderLogic
import Debug.Trace
import qualified Logic.Instances.Parameterized as Param
import Logic.Instances.Chiou (AtomicFunction(..))
import Logic.Logic (Logic(..))
import Logic.Predicate (PredicateLogic(..), convertPred, Skolem(..), showForm {-, toPropositional, InfixPred(..), freeVars, substitute-})
import Test.HUnit

-- Skolem instance for Formula String String
instance Skolem Param.V String where
    skolem (Param.V s) = "Sk(" ++ s ++ ")"

instance Show (Param.Formula String String) where
    show = showForm

tests :: [Test]
tests = 
    [ TestCase (assertEqual "Chiou test 1"
                            (convertPred vc pc AtomicConstant (t2 formula') :: Sentence)
                            (t1 formula))
    , TestCase (assertEqual "Chiou test 2"
                            (convertPred Param.V pc fc (t1 formula) :: Param.Formula String String)
                            (t2 formula'))
    ]
    where
      t2 formula = trace ("\nParameterized:" ++ showForm formula) formula
      t1 formula = trace ("\nChiou:         " ++ show formula) formula

-- |Use the class operators to build a Chiou Sentence
formula :: Sentence
formula = for_all [x'] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
    where
      h vs = pApp "h" vs
      m vs = pApp "m" vs
      s vs = pApp "s" vs
      x' = "x"
      x = var x'

-- |Use the same class operators to build a Parameterized Formula.
formula' :: Param.Formula String String
formula' = for_all [x'] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
    where
      h vs = pApp "h" vs
      m vs = pApp "m" vs
      s vs = pApp "s" vs
      x' = "x"
      x = var x'


vc :: Param.V -> String
vc (Param.V s) = s

pc :: String -> String
pc = id

fc :: AtomicFunction -> String
fc (AtomicConstant s) = s
fc _ = error "FIXME: fc"
