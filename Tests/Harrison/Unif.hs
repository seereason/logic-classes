{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Harrison.Unif
    ( tests
    ) where

import FOL (IsTerm(fApp, vt), tsubst)
import Lib (Failing(..), failing)
import Unif (fullunify)
import FOL (Term)
import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)
import FOL (FName)

tests :: Test
tests = TestLabel "Data.Logic.Tests.Harrison.Unif" $ TestList [test01]

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestCase $ assertEqual "Unify tests" expected input
    where input = map unify_and_apply eqss
          expected = map Success $
                      [[(fApp "f" [fApp "f" [vt "z"],fApp "g" [vt "y"]],
                        fApp "f" [fApp "f" [vt "z"],fApp "g" [vt "y"]])],
                      [(fApp "f" [vt "y",vt "y"],fApp "f" [vt "y",vt "y"])],
                      [(fApp "f" [fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]],
                                  fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]]],
                        fApp "f" [fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]],
                                  fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]]]),
                       (fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]],
                        fApp "f" [fApp "f" [vt "x3",vt "x3"],fApp "f" [vt "x3",vt "x3"]]),
                       (fApp "f" [vt "x3",vt "x3"],
                        fApp "f" [vt "x3",vt "x3"])]]
          unify_and_apply eqs =
              mapM app eqs
              where
                app (t1, t2) = failing Failure (\ i -> Success (tsubst i t1, tsubst i t2)) (fullunify eqs)
          eqss :: [[(Term FName String, Term FName String)]]
          eqss =  [ [(fApp "f" [vt "x", fApp "g" [vt "y"]], fApp "f" [fApp "f" [vt "z"], vt "w"])]
                  , [(fApp "f" [vt "x", vt "y"], fApp "f" [vt "y", vt "x"])]
                  -- , [(fApp "f" [vt "x", fApp "g" [vt "y"]], fApp "f" [vt "y", vt "x"])] -- cyclic
                  , [(vt "x0", fApp "f" [vt "x1", vt "x1"]),
                     (vt "x1", fApp "f" [vt "x2", vt "x2"]),
                     (vt "x2", fApp "f" [vt "x3", vt "x3"])] ]
