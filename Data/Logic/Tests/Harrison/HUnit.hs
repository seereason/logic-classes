{-# LANGUAGE MultiParamTypeClasses, RankNTypes #-}
-- | HUnit types with a type parameter.
module Data.Logic.Tests.Harrison.HUnit
    ( Test(..)
    , Assertion
    , T.assertEqual
    , convert
    , TestFormula
    , TestFormulaEq
    ) where

import Data.Logic.Classes.Apply (Apply)
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula)
import Data.Logic.Classes.Term (Term)
import Data.Logic.Types.Harrison.FOL (Function(..))
import Data.String (IsString(fromString))
import qualified Test.HUnit as T

type Assertion t = IO ()

-- | Provide a phantom type for a test
data Test t
  = TestCase (Assertion t)
  | TestList [Test t]
  | TestLabel String (Test t)
  | Test0 T.Test

convert :: Test t -> T.Test
convert (TestCase assertion) = T.TestCase assertion
convert (TestList tests) = T.TestList (map convert tests)
convert (TestLabel label test) = T.TestLabel label (convert test)
convert (Test0 test) = test

class (FirstOrderFormula formula atom v,
       Apply atom p term,
       Term term v f,
       Eq formula, Ord formula, Show formula,
       Eq p,
       IsString v, IsString p, IsString f, Ord f, Ord p,
       Eq term, Show term, Ord term,
       Show v) => TestFormula formula atom term v p f

class (FirstOrderFormula formula atom v,
       AtomEq atom p term,
       Term term v f,
       Eq formula, Ord formula, Show formula,
       Eq p,
       IsString v, IsString p, IsString f, Ord f, Ord p,
       Eq term, Show term, Ord term,
       Show v) => TestFormulaEq formula atom term v p f

{-
type Test' = forall formula atom term v p f. TestFormula formula atom term v p f => Test formula
type Formula' = forall formula atom term v p f. TestFormula formula atom term v p f => formula
type TestEq' = forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
type FormulaEq' = forall formula atom term v p f. TestFormulaEq formula atom term v p f => formula
-}

instance IsString Function where
    fromString = FName
