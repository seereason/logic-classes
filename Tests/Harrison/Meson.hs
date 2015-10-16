{-# LANGUAGE FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}
module Harrison.Meson where

import Control.Applicative.Error (Failing(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import FOL (pApp)
import Formulas ((.&.), (.=>.), (.|.))
import FOL (exists, for_all)
import Formulas ((.~.))
import Skolem (HasSkolem(..))
import FOL (IsTerm(vt, fApp))
import FOL (generalize)
import Prop (list_conj)
import Meson(meson)
import Skolem (MyFormula, simpdnf')
import Skolem (runSkolem, askolemize)
import Data.String (IsString(fromString))
import Prelude hiding (negate)
import Test.HUnit (Test(TestCase, TestLabel, TestList), assertEqual)
import Tableaux (Depth(Depth))

import Common (render)
import Harrison.Resolution (dpExampleFm)

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Meson" $
        TestList [test01, test02]

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestLabel "Data.Logic.Tests.Harrison.Meson" $ TestCase $ assertEqual "meson dp example (p. 220)" expected input
    where input = runSkolem (meson (Just (Depth 10)) (dpExampleFm :: MyFormula))
          expected = Set.singleton (
                                    -- Success ((Map.empty, 0, 0), 8)
                                    Success ((Map.fromList [(fromString "_0",vt' "_6"),
                                                            (fromString "_1",vt' "_2"),
                                                            (fromString "_10",fApp (toSkolem "z") [vt' "_6",vt' "_7"]),
                                                            (fromString "_11",fApp (toSkolem "z") [vt' "_6",vt' "_7"]),
                                                            (fromString "_12",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_13",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_14",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_15",fApp (toSkolem "z") [vt' "_12",vt' "_13"]),
                                                            (fromString "_16",fApp (toSkolem "z") [vt' "_12",vt' "_13"]),
                                                            (fromString "_17",fApp (toSkolem "z") [vt' "_12",vt' "_13"]),
                                                            (fromString "_3",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_4",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_5",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_7",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_8",fApp (toSkolem "z") [vt' "_0",vt' "_1"]),
                                                            (fromString "_9",fApp (toSkolem "z") [vt' "_6",vt' "_7"])],0,18),Depth 8)
                                   )
          vt' = vt . fromString

test02 :: Test
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
                                                                                        (((f [x,y]) .&. (g [x,y])) .=>. ((g [x,z]) .&. (g [z,z]))))))) :: MyFormula))
                                    (render ((.~.) (generalize dpExampleFm)))),
              TestCase (assertEqual "meson dp example, step 4 (p. 220)"
                                    (render (for_all "x" . for_all "y" $
                                             f[x,y] .&.
                                             ((.~.)(f[y, sk1[x, y]]) .|. ((.~.)(f[sk1[x,y], sk1[x, y]]))) .|.
                                             (f[x,y] .&. g[x,y]) .&.
                                             (((.~.)(g[x,sk1[x,y]])) .|. ((.~.)(g[sk1[x,y], sk1[x,y]])))))
                                    (render (runSkolem (askolemize ((.~.) (generalize dpExampleFm))) :: MyFormula))),
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
                                    (Set.map (Set.map render) (simpdnf' (runSkolem (askolemize ((.~.) (generalize dpExampleFm))) :: MyFormula)))),
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
                                    (Set.map render ((Set.map list_conj (simpdnf' (runSkolem (askolemize ((.~.) (generalize dpExampleFm)))))) :: Set.Set MyFormula)))]
    where f = pApp "F"
          g = pApp "G"
          sk1 = fApp (toSkolem "z")
          x = vt "x"
          y = vt "y"
          z = vt "z"

{-
askolemize (simpdnf (generalize dpExampleFm)) ->
 <<forall x y. F(x,y) /\ (~F(y,f_z(x,y)) \/ ~F(f_z(x,y), f_z(x,y))) \/ (F(x,y) /\ G(x,y)) /\ (~G(x,f_z(x,y)) \/ ~G(f_z(x,y),f_z(x,y)))>>
-}
