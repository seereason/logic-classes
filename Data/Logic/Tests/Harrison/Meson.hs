{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Data.Logic.Tests.Harrison.Meson where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Logic.Classes.Equals (pApp)
import Data.Logic.Classes.Combine ((.&.), (.=>.), (.|.))
import Data.Logic.Classes.Constants (true)
import Data.Logic.Classes.FirstOrder (exists, for_all)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(vt, fApp))
import Data.Logic.Harrison.FOL (generalize, list_conj)
import Data.Logic.Harrison.Meson(meson)
import Data.Logic.Harrison.Normal (simpdnf)
import Data.Logic.Harrison.Skolem (runSkolem, askolemize)
import Data.Logic.Tests.Common (render)
import Data.Logic.Tests.Harrison.Resolution (dpExampleFm)
import Data.Logic.Tests.HUnit
import Data.Logic.Types.Harrison.Equal (FOLEQ)
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula)
import Data.String (IsString(fromString))
import Prelude hiding (negate)
-- import Test.HUnit (Test(TestCase, TestLabel), assertEqual)

tests :: Test (Formula FOLEQ)
tests = TestLabel "Data.Logic.Tests.Harrison.Meson" $
        TestList [test01, test02]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: Test (Formula FOLEQ)
test01 = TestLabel "Data.Logic.Tests.Harrison.Meson" $ TestCase $ assertEqual "meson dp example (p. 220)" expected input
    where input = runSkolem (meson (Just 10) (dpExampleFm :: Formula FOLEQ))
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

test02 :: Test (Formula FOLEQ)
test02 =
    TestLabel "Data.Logic.Tests.Harrison.Meson" $
    TestList [TestCase (assertEqual "meson dp example, step 1 (p. 220)"
                                    (render (exists "x" (exists "y" (for_all "z" (((f [x,y]) .=>. ((f [y,z]) .&. (f [z,z]))) .&.
                                                                                  (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z]))))))))
                                    (render dpExampleFm)),
              TestCase (assertEqual "meson dp example, step 2 (p. 220)"
                                    (render (exists "x" (exists "y" (for_all "z" (((f [x,y]) .=>. ((f [y,z]) .&. (f [z,z]))) .&.
                                                                                  (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z]))))))))
                                    (render (generalize dpExampleFm))),
              TestCase (assertEqual "meson dp example, step 3 (p. 220)"
                                    (render ((.~.)(exists "x" (exists "y" (for_all "z" (((f [x,y]) .=>. ((f [y,z]) .&. (f [z,z]))) .&.
                                                                                        (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z]))))))) :: Formula FOLEQ))
                                    (render ((.~.) (generalize dpExampleFm)))),
              TestCase (assertEqual "meson dp example, step 4 (p. 220)"
                                    (render (for_all "x" . for_all "y" $
                                             f[x,y] .&.
                                             ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                             (f[x,y] .&. g[x,y]) .&.
                                             (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))))
                                    (render (runSkolem (askolemize ((.~.) (generalize dpExampleFm))) :: Formula FOLEQ))),
              TestCase (assertEqual "meson dp example, step 5 (p. 220)"
                                    (Set.map (Set.map render)
                                     (Set.fromList
                                      [Set.fromList [for_all "x" . for_all "y" $
                                                     f[x,y] .&.
                                                     ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                                     (f[x,y] .&. g[x,y]) .&.
                                                     (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))]]))
{-
[[<<forall x y.
      F(x,y) /\
      (~F(y,f_z(x,y)) \/ ~F(f_z(x,y),f_z(x,y))) \/
      (F(x,y) /\ G(x,y)) /\
      (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y))) >>]]
-}
                                    (Set.map (Set.map render) (simpdnf (runSkolem (askolemize ((.~.) (generalize dpExampleFm))) :: Formula FOLEQ)))),
              TestCase (assertEqual "meson dp example, step 6 (p. 220)"
                                    (Set.map render
                                     (Set.fromList [for_all "x" . for_all "y" $
                                                    f[x,y] .&.
                                                    ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                                    (f[x,y] .&. g[x,y]) .&.
                                                    (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))]))
{-
[<<forall x y.
     F(x,y) /\
     (~F(y,f_z(x,y)) \/ ~F(f_z(x,y),f_z(x,y))) \/
     (F(x,y) /\ G(x,y)) /\ 
     (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y)))>>]
-}
                                    (Set.map render ((Set.map list_conj (simpdnf (runSkolem (askolemize ((.~.) (generalize dpExampleFm)))))) :: Set.Set (Formula FOLEQ))))]
    where f = pApp "F"
          g = pApp "G"
          sk1 = fApp (toSkolem 1)
          x = vt "x"
          y = vt "y"
          z = vt "z"

{-
askolemize (simpdnf (generalize dpExampleFm)) ->
 <<forall x y. F(x,y) /\ (~F(y,f_z(x,y)) \/ ~F(f_z(x,y), f_z(x,y))) \/ (F(x,y) /\ G(x,y)) /\ (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y)))>>
-}
