{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures #-}
module Test.New where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Generics (Data, Typeable, listify)
import qualified Data.Set as S
import Logic.Clause (Literal)
import Logic.FirstOrder (FirstOrderLogic, convertFOF, fromSkolem)
import Logic.KnowledgeBase (loadKB, theoremKB, getKB)
import Logic.Logic (Logic(..))
import Logic.Monad (runNormal, runProver')
import Logic.Normal (Implicative)
import Logic.NormalForm (simplify, negationNormalForm, prenexNormalForm, skolemNormalForm, clauseNormalForm, trivial)
import Logic.Satisfiable (satisfiable) 
import Test.HUnit
import Test.Types

skolemNumber :: FirstOrderLogic formula term v p f => f -> [Int]
skolemNumber f = maybe [] (: []) (fromSkolem f)

-- Knowledge Base tests.
kbTests :: (Implicative inf formula, FirstOrderLogic formula term v p f, Show formula, Literal formula, Data formula, Ord formula) =>
           (String, [TestFormula inf formula term v p f], [TestFormula inf formula term v p f]) -> Test
kbTests (kbname, knowledge, conjectures) =
    TestLabel (kbname ++ " knowledge base") $ TestList $
    map conjectureTests conjectures
    where
      conjectureTests c =
          doTest (c { name = name c ++ " with " ++ kbname ++ " knowledge base"
                    , formula = conj (map formula knowledge) .=>. formula c })
      conj [] = error "conj []"
      conj [x] = x
      conj (x:xs) = x .&. conj xs
