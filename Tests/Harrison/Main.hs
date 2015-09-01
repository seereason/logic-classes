{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeSynonymInstances #-}
module Harrison.Main (tests) where

import Data.Logic.Classes.Pretty (pretty)
import qualified Data.Logic.Harrison.Lib as Lib
import qualified Harrison.Equal as Equal
import qualified Harrison.FOL as FOL
import qualified Harrison.Meson as Meson
import qualified Harrison.Prop as Prop
import qualified Harrison.Resolution as Resolution
import qualified Harrison.Skolem as Skolem
import qualified Harrison.Unif as Unif
import Data.Logic.Types.Harrison.Equal (FOLEQ, PredName)
import Data.Logic.Types.Harrison.FOL (FOL, TermType, Function)
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import Data.Logic.HUnit
import qualified Test.HUnit as T
--import Data.String (IsString)

instance TestFormula (Formula FOL) FOL TermType String String Function
instance TestFormulaEq (Formula FOLEQ) FOLEQ TermType String PredName Function

instance Show (Formula FOL) where
    show = show . pretty

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
         , convert (Equal.tests :: Test (Formula FOLEQ))
         , convert (Meson.tests :: Test (Formula FOLEQ))
         ]
