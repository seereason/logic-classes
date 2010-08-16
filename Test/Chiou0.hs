{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Test.Chiou0 where

import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadIO, liftIO)
import Data.Map (fromList)
import qualified Data.Set as S
import Data.String (IsString(..))
--import Logic.Chiou.FirstOrderLogic (Sentence(..), CTerm, Quantifier(..), Connective(..))
--import qualified Logic.Chiou.FirstOrderLogic as C
--import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..), NormalTerm(..){-, ConjunctiveNormalForm(..), distributeAndOverOr -})
import qualified Logic.FirstOrder as Logic
import Logic.FirstOrder (FirstOrderLogic(..), Term(..), Skolem(..))
import Logic.Implicative (Implicative(..))
import Logic.Instances.Native
import Logic.KnowledgeBase (loadKB, theoremKB {-, askKB, showKB-})
import Logic.Logic (Logic(..), Boolean(..))
import Logic.Monad (NormalT, runNormal, ProverT, runProver')
import Logic.NormalForm (disjunctiveNormalForm)
import Logic.Resolution (SetOfSupport)
import Test.HUnit
import Test.Types (V(..), Pr(..), AtomicFunction(..))

tests :: Test
tests = TestLabel "Chiou0" $ TestList [loadTest, proofTest1, proofTest2]

loadTest :: Test
loadTest =
    TestCase (assertEqual "Chiuo0 - loadKB test" expected (runProver' (loadKB sentences)))
    where
      expected :: [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
      expected = [(Nothing,[makeINF (S.fromList []) (S.fromList [(pApp (Pr "Dog") [fApp (toSkolem 1) []])]),
                            makeINF (S.fromList []) (S.fromList [(pApp (Pr "Owns") [fApp ("Jack") [],fApp (toSkolem 1) []])])]),
                  (Nothing,[makeINF (S.fromList [(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [var ("x"),var ("y")])]) (S.fromList [(pApp (Pr "AnimalLover") [var ("x")])])]),
                  (Nothing,[makeINF (S.fromList [(pApp (Pr "Animal") [var ("y")]),(pApp (Pr "AnimalLover") [var ("x")]),(pApp (Pr "Kills") [var ("x"),var ("y")])]) (S.fromList [])]),
                  (Nothing,[makeINF (S.fromList []) (S.fromList [(pApp (Pr "Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),(pApp (Pr "Kills") [fApp ("Jack") [],fApp ("Tuna") []])])]),
                  (Nothing,[makeINF (S.fromList []) (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []])])]),
                  (Nothing,[makeINF (S.fromList [(pApp (Pr "Cat") [var ("x")])]) (S.fromList [(pApp (Pr "Animal") [var ("x")])])])]

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runProver' (loadKB sentences >> theoremKB (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []]))))

inf' l1 l2 = makeINF (S.fromList l1) (S.fromList l2)

proof1 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (PTerm V AtomicFunction))
proof1 = ( False,
           [(makeINF (S.fromList [(pApp (Pr "Kills") [fApp ("Jack") [],fApp ("Tuna") []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList []) (S.fromList [(pApp (Pr "Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "AnimalLover") [fApp ("Curiosity") []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Curiosity") [],var ("y")])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "AnimalLover") [fApp ("Curiosity") []]),(pApp (Pr "Cat") [fApp ("Tuna") []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "Owns") [fApp ("Curiosity") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []]),(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Curiosity") [],var ("y")])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "AnimalLover") [fApp ("Curiosity") []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []]),(pApp (Pr "Owns") [fApp ("Curiosity") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Curiosity") [],var ("y")])]) (S.fromList []),fromList []),
            (makeINF (S.fromList [(pApp (Pr "Owns") [fApp ("Curiosity") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList [])])

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runProver' (loadKB sentences >> theoremKB conjecture)))
    where
      conjecture :: Formula V Pr AtomicFunction
      conjecture = (pApp "Kills" [fApp "Curiosity" [], fApp (Fn "Tuna") []])

proof2 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (PTerm V AtomicFunction))
proof2 = (True,
          [(makeINF (S.fromList [(pApp (Pr "Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList []) (S.fromList [(pApp (Pr "Kills") [fApp ("Jack") [],fApp ("Tuna") []])]),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "AnimalLover") [fApp ("Jack") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Jack") [],var ("y")])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "AnimalLover") [fApp ("Jack") []]),(pApp (Pr "Cat") [fApp ("Tuna") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "Owns") [fApp ("Jack") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []]),(pApp (Pr "Dog") [fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []]),(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Jack") [],var ("y")])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "AnimalLover") [fApp ("Jack") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Animal") [fApp ("Tuna") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []]),(pApp (Pr "Owns") [fApp ("Jack") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []]),(pApp (Pr "Dog") [fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Dog") [var ("y")]),(pApp (Pr "Owns") [fApp ("Jack") [],var ("y")])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Cat") [fApp ("Tuna") []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Owns") [fApp ("Jack") [],fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList [(pApp (Pr "Dog") [fApp (toSkolem 1) []])]) (S.fromList []),fromList []),
           (makeINF (S.fromList []) (S.fromList []),fromList [])])

testProof :: MonadIO m => String -> (Formula V Pr AtomicFunction, Bool, [ImplicativeNormalForm V Pr AtomicFunction]) -> ProverT (ImplicativeNormalForm V Pr AtomicFunction) (NormalT V (PTerm V AtomicFunction) m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeNormalForm V Pr AtomicFunction) (NormalT V (PTerm V AtomicFunction) m) [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
loadCmd = loadKB sentences

sentences :: [Formula V Pr AtomicFunction]
sentences = [exists ["x"] ((pApp "Dog" [var "x"]) .&. (pApp "Owns" [fApp "Jack" [], var "x"])),
             for_all ["x"] (((exists ["y"] (pApp "Dog" [var "y"])) .&. (pApp "Owns" [var "x", var "y"])) .=>. (pApp "AnimalLover" [var "x"])),
             for_all ["x"] ((pApp "AnimalLover" [var "x"]) .=>. (for_all ["y"] ((pApp "Animal" [var "y"]) .=>. ((.~.) (pApp "Kills" [var "x", var "y"]))))),
             (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []]) .|. (pApp "Kills" [fApp "Curiosity" [], fApp "Tuna" []]),
             pApp "Cat" [fApp "Tuna" []],
             for_all ["x"] ((pApp "Cat" [var "x"]) .=>. (pApp "Animal" [var "x"]))]
