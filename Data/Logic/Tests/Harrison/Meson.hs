{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Meson where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Logic.Classes.Equals (varAtomEq, substAtomEq)
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Harrison.Meson(meson)
import Data.Logic.Harrison.Skolem (runSkolem)
import Data.Logic.Harrison.Tableaux (unifyAtomsEq)
import Data.Logic.Tests.Harrison.Resolution (dpExampleFm)
import Data.Logic.Tests.Harrison.HUnit
import Data.Logic.Types.Harrison.Equal (FOLEQ)
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula)
import Data.String (IsString(fromString))
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestLabel), assertEqual)

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: Test (Formula FOLEQ)
test01 = TestLabel "Data.Logic.Tests.Harrison.Meson" $ TestCase $ assertEqual "meson dp example (p. 220)" expected input
    where input = runSkolem (meson unifyAtomsEq varAtomEq substAtomEq (Just 10) (dpExampleFm :: Formula FOLEQ))
          expected = Set.singleton (
                                    -- Success ((Map.empty, 0, 0), 8)
                                    Success ((Map.fromList [(fromString "_0",vt' "_6"),
                                                            (fromString "_1",vt' "_2"),
                                                            (fromString "_10",fApp (toSkolem 1) [vt' "_6",vt' "_7"]),
                                                            (fromString "_11",fApp (toSkolem 1) [vt' "_6",vt' "_7"]),
                                                            (fromString "_12",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_13",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_14",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_15",fApp (toSkolem 1) [vt' "_12",vt' "_13"]),
                                                            (fromString "_16",fApp (toSkolem 1) [vt' "_12",vt' "_13"]),
                                                            (fromString "_17",fApp (toSkolem 1) [vt' "_12",vt' "_13"]),
                                                            (fromString "_3",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_4",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_5",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_7",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_8",fApp (toSkolem 1) [vt' "_0",vt' "_1"]),
                                                            (fromString "_9",fApp (toSkolem 1) [vt' "_6",vt' "_7"])],0,18),8)
                                   )
          vt' = vt . fromString
