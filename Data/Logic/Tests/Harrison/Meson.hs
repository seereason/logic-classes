{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Meson where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Logic.Harrison.Meson(meson)
import Data.Logic.Normal.Skolem (runSkolem)
import Data.Logic.Tests.Harrison.Resolution (dpExampleFm)
import Data.Logic.Tests.Harrison.HUnit
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestLabel), assertEqual)

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test01 = TestLabel "Data.Logic.Tests.Harrison.Meson" $ TestCase $ assertEqual "meson dp example (p. 220)" expected input
    where input = runSkolem (meson (Just 10) (dpExampleFm :: formula))
          expected = Set.singleton (Success ((Map.empty, 0, 0), 8))
