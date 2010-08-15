{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Test.Chiou0 where

import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadIO, liftIO)
import Data.Map (fromList)
import Data.String (IsString(..))
import Logic.Chiou.FirstOrderLogic (Sentence(..), CTerm, Quantifier(..), Connective(..))
import qualified Logic.Chiou.FirstOrderLogic as C
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..), NormalTerm(..){-, ConjunctiveNormalForm(..), distributeAndOverOr -})
import qualified Logic.FirstOrder as Logic
import Logic.FirstOrder (FirstOrderLogic(..), Term(..), Skolem(..))
import Logic.KnowledgeBase (loadKB, theoremKB {-, askKB, showKB-})
import Logic.Logic (Logic(..), Boolean(..))
import Logic.Monad (SkolemT, runSkolem, ProverT, runProver')
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
      expected = [(Nothing,[INF [] [(pApp (Pr "Dog") [fApp (Skolem 1) []])],INF [] [(pApp (Pr "Owns") [fApp (Fn "Jack") [],fApp (Skolem 1) []])]]),
                  (Nothing,[INF [(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [var (V "x"),var (V "y")])] [(pApp (Pr "AnimalLover") [var (V "x")])]]),
                  (Nothing,[INF [(pApp (Pr "Animal") [var (V "y")]),(pApp (Pr "AnimalLover") [var (V "x")]),(pApp (Pr "Kills") [var (V "x"),var (V "y")])] []]),
                  (Nothing,[INF [] [(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []]),(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []])]]),
                  (Nothing,[INF [] [(pApp (Pr "Cat") [fApp (Fn "Tuna") []])]]),
                  (Nothing,[INF [(pApp (Pr "Cat") [var (V "x")])] [(pApp (Pr "Animal") [var (V "x")])]])]

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runProver' (loadKB sentences >> theoremKB (Predicate "Kills" [C.Function (Fn "Jack") [], C.Function (Fn "Tuna") []]))))

proof1 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (CTerm V AtomicFunction))
proof1 = ( False,
           [(INF [(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []])] [],fromList []),
            (INF [] [(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])],fromList []),
            (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "AnimalLover") [fApp (Fn "Curiosity") []])] [],fromList []),
            (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList []),
            (INF [(pApp (Pr "AnimalLover") [fApp (Fn "Curiosity") []]),(pApp (Pr "Cat") [fApp (Fn "Tuna") []])] [],fromList []),
            (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList []),
            (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList []),
            (INF [(pApp (Pr "AnimalLover") [fApp (Fn "Curiosity") []])] [],fromList []),
            (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []]),(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList []),
            (INF [(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList []),
            (INF [(pApp (Pr "Owns") [fApp (Fn "Curiosity") [],var (V "y")])] [],fromList [])])

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runProver' (loadKB sentences >> theoremKB (Predicate "Kills" [C.Function (Fn "Curiosity") [], C.Function (Fn "Tuna") []]))))

proof2 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (CTerm V AtomicFunction))
proof2 = (True,[(INF [(pApp (Pr "Kills") [fApp (Fn "Curiosity") [],fApp (Fn "Tuna") []])] [],fromList []),
                (INF [] [(pApp (Pr "Kills") [fApp (Fn "Jack") [],fApp (Fn "Tuna") []])],fromList []),
                (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "AnimalLover") [fApp (Fn "Jack") []])] [],fromList []),
                (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "AnimalLover") [fApp (Fn "Jack") []]),(pApp (Pr "Cat") [fApp (Fn "Tuna") []])] [],fromList []),
                (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")])] [],fromList []),
                (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "AnimalLover") [fApp (Fn "Jack") []])] [],fromList []),
                (INF [(pApp (Pr "Animal") [fApp (Fn "Tuna") []])] [],fromList []),
                (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []]),(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []]),(pApp (Pr "Dog") [var (V "y2")])] [],fromList []),
                (INF [(pApp (Pr "Dog") [var (V "y2")]),(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "Cat") [fApp (Fn "Tuna") []])] [],fromList []),
                (INF [(pApp (Pr "Owns") [fApp (Fn "Jack") [],var (V "y")])] [],fromList []),
                (INF [(pApp (Pr "Dog") [var (V "y2")])] [],fromList []),
                (INF [] [],fromList [])])

testProof :: MonadIO m => String -> (Sentence V Pr AtomicFunction, Bool, [ImplicativeNormalForm V Pr AtomicFunction]) -> ProverT (ImplicativeNormalForm V Pr AtomicFunction) (SkolemT V (CTerm V AtomicFunction) m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeNormalForm V Pr AtomicFunction) (SkolemT V (CTerm V AtomicFunction) m) [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
loadCmd = loadKB sentences

sentences :: [Sentence V Pr AtomicFunction]
sentences = [Quantifier ExistsCh ["x"] (Connective (Predicate "Dog" [C.Variable "x"]) And (Predicate "Owns" [C.Function "Jack" [], C.Variable "x"])),
             Quantifier ForAll ["x"] (Connective (Connective (Quantifier ExistsCh ["y"] (Predicate "Dog" [C.Variable "y"])) And
                                                             (Predicate "Owns" [C.Variable "x", C.Variable "y"])) Imply
                                                 (Predicate "AnimalLover" [C.Variable "x"])),

             Quantifier ForAll ["x"] (Connective (Predicate "AnimalLover" [C.Variable "x"]) Imply
                                                 (Quantifier ForAll ["y"] (Connective (Predicate "Animal" [C.Variable "y"]) Imply
                                                                                      (Not (Predicate "Kills" [C.Variable "x", C.Variable "y"]))))),

             Connective (Predicate "Kills" [C.Function "Jack" [], C.Function "Tuna" []]) Or
                        (Predicate "Kills" [C.Function "Curiosity" [], C.Function "Tuna" []]),
             Predicate "Cat" [C.Function "Tuna" []],
             Quantifier ForAll ["x"] (Connective (Predicate "Cat" [C.Variable "x"]) Imply (Predicate "Animal" [C.Variable "x"]))]
