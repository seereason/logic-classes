{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Test.Chiou0 where

import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadIO, liftIO)
import Data.String (IsString(..))
import Logic.Chiou.FirstOrderLogic (Sentence(..), Term, Quantifier(..), Connective(..))
import qualified Logic.Chiou.FirstOrderLogic as C
import Logic.Chiou.Monad (ProverT, runProver')
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..), NormalTerm(..){-, ConjunctiveNormalForm(..), distributeAndOverOr -})
import Logic.Chiou.KnowledgeBase (loadKB, theoremKB {-, askKB, showKB-})
import qualified Logic.FirstOrder as Logic
import Logic.FirstOrder (FirstOrderLogic(..), Skolem(..))
import Logic.Logic (Logic(..), Boolean(..))
import Logic.Monad (SkolemT, runSkolem)
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
      expected = [(Nothing,[INF [] [NFPredicate (Pr "Dog") [Function (Skolem 1) []]],INF [] [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Function (Skolem 1) []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Variable (V "x"),Variable (V "y")]] [NFPredicate (Pr "AnimalLover") [Variable (V "x")]]]),
                  (Nothing,[INF [NFPredicate (Pr "Animal") [Variable (V "y")],NFPredicate (Pr "AnimalLover") [Variable (V "x")],NFPredicate (Pr "Kills") [Variable (V "x"),Variable (V "y")]] []]),
                  (Nothing,[INF [] [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []],NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [] [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Cat") [Variable (V "x")]] [NFPredicate (Pr "Animal") [Variable (V "x")]]])]

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runProver' (loadKB sentences >> theoremKB (Predicate "Kills" [C.Function (Fn "Jack") [], C.Function (Fn "Tuna") []]))))

proof1 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (NormalTerm V AtomicFunction))
proof1 = ( False,
           [(INF [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]] [],[]),
            (INF [] [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]],[]),
            (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),
            (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),
            (INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),
            (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),
            (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),
            (INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),
            (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),
            (INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),
            (INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[])])

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runProver' (loadKB sentences >> theoremKB (Predicate "Kills" [C.Function (Fn "Curiosity") [], C.Function (Fn "Tuna") []]))))

proof2 :: (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (NormalTerm V AtomicFunction))
proof2 = (True,[(INF [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]] [],[]),
                (INF [] [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]],[]),
                (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),
                (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),
                (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),
                (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),
                (INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),
                (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),
                (INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),
                (INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),
                (INF [NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),
                (INF [] [],[])])

testProof :: MonadIO m => String -> (Sentence V Pr AtomicFunction, Bool, [ImplicativeNormalForm V Pr AtomicFunction]) -> ProverT (ImplicativeNormalForm V Pr AtomicFunction) (SkolemT V (Term V AtomicFunction) m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeNormalForm V Pr AtomicFunction) (SkolemT V (Term V AtomicFunction) m) [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
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
