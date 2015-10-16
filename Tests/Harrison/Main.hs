{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, RankNTypes, TypeSynonymInstances #-}
module Harrison.Main (tests) where

import Pretty (pPrint)
import qualified Lib as Lib
import qualified Harrison.Equal as Equal
import qualified Harrison.FOL as FOL
import qualified Harrison.Meson as Meson
import qualified Harrison.Prop as Prop
import qualified Harrison.Resolution as Resolution
import qualified Harrison.Skolem as Skolem
import qualified Harrison.Unif as Unif
import Test.HUnit
import FOL (MyFormula1)

instance Show MyFormula1 where
    show = show . pPrint

main = runTestTT tests

tests :: Test
tests =
    TestList
         [ Lib.tests
         , Prop.tests
         , FOL.tests1
         , FOL.tests2
         , Unif.tests
         , Skolem.tests
         , Resolution.tests
         , Equal.tests
         , Meson.tests
         ]
