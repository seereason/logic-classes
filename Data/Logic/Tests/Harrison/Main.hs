{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeSynonymInstances #-}
module Data.Logic.Tests.Harrison.Main (tests) where

import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula)
import Data.Logic.Classes.Term (Term)
import qualified Data.Logic.Harrison.Lib as Lib
-- import qualified Data.Logic.Tests.Harrison.Equal as Equal
import qualified Data.Logic.Tests.Harrison.FOL as FOL
import qualified Data.Logic.Tests.Harrison.Prop as Prop
import qualified Data.Logic.Tests.Harrison.Resolution as Resolution
import qualified Data.Logic.Tests.Harrison.Skolem as Skolem
import qualified Data.Logic.Tests.Harrison.Unif as Unif
import Data.Logic.Types.Harrison.Equal (FOLEQ, PredName)
import Data.Logic.Types.Harrison.FOL (FOL, TermType, Function)
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import Data.Logic.Tests.Harrison.HUnit
import qualified Test.HUnit as T
import Data.String (IsString)

instance TestFormula (Formula FOL) FOL TermType String String Function
instance TestFormulaEq (Formula FOLEQ) FOLEQ TermType String PredName Function

main = T.runTestTT tests

tests :: T.Test
tests =
    T.TestList
         [ Lib.tests
         , Prop.tests
         , convert (FOL.tests1 :: Test (Formula FOL))
         , convert (FOL.tests2 :: Test (Formula FOLEQ))
         , Unif.tests
         , Skolem.tests
         , convert (Resolution.tests :: Test (Formula FOLEQ))
         -- , convert (Equal.tests :: Test (Formula FOLEQ))
         ]
