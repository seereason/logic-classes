{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Tests.Harrison.Unif
    ( tests
    ) where

import Control.Applicative.Error (Failing(..), failing)
import Data.Logic.Classes.Term (Term(fApp, vt))
import Data.Logic.Harrison.FOL (tsubst)
import Data.Logic.Harrison.Unif (fullUnify)
import Data.Logic.Types.Harrison.FOL (TermType)
import Data.Logic.Tests.Harrison.HUnit ()
import Test.HUnit (Test(TestCase, TestList, TestLabel), assertEqual)

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
                app (t1, t2) = failing Failure (\ i -> Success (tsubst i t1, tsubst i t2)) (fullUnify eqs)
          eqss :: [[(TermType, TermType)]]
          eqss =  [ [(fApp "f" [vt "x", fApp "g" [vt "y"]], fApp "f" [fApp "f" [vt "z"], vt "w"])]
                  , [(fApp "f" [vt "x", vt "y"], fApp "f" [vt "y", vt "x"])]
                  -- , [(fApp "f" [vt "x", fApp "g" [vt "y"]], fApp "f" [vt "y", vt "x"])] -- cyclic
                  , [(vt "x0", fApp "f" [vt "x1", vt "x1"]),
                     (vt "x1", fApp "f" [vt "x2", vt "x2"]),
                     (vt "x2", fApp "f" [vt "x3", vt "x3"])] ]
