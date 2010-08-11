{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Test.Chiou0 where

import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadIO, liftIO)
import Data.String (IsString(..))
import Logic.Chiou.FirstOrderLogic (Sentence(..), Term(..), Quantifier(..), Connective(..))
import Logic.Chiou.Monad (ProverT, runProverT)
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..){-, ConjunctiveNormalForm(..), distributeAndOverOr -})
import Logic.Chiou.KnowledgeBase (loadKB, theoremKB {-, askKB, showKB-})
import Logic.Chiou.Resolution (SetOfSupport)
import Logic.FirstOrder (FirstOrderLogic(..), Skolem(..))
import Logic.Logic (Logic(..), Boolean(..))
import Logic.NormalForm (disjunctiveNormalForm)
import Test.HUnit
import Test.Types (V(..), Pr(..), AtomicFunction(..))

tests :: Test
tests = TestLabel "Chiou0" $ TestList [loadTest, proofTest1, proofTest2]

loadTest :: Test
loadTest =
    TestCase (assertEqual "Chiuo0 - loadKB test" expected (runIdentity (runProverT (loadKB sentences))))
    where
      expected :: [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
      expected = [(Nothing,[INF [] [NFPredicate (Pr "Dog") [Function (Skolem 1) []]],INF [] [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Function (Skolem 1) []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Variable (V "x"),Variable (V "y")]] [NFPredicate (Pr "AnimalLover") [Variable (V "x")]]]),
                  (Nothing,[INF [NFPredicate (Pr "AnimalLover") [Variable (V "x")],NFPredicate (Pr "Animal") [Variable (V "y")],NFPredicate (Pr "Kills") [Variable (V "x"),Variable (V "y")]] []]),
                  (Nothing,[INF [] [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []],NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [] [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Cat") [Variable (V "x")]] [NFPredicate (Pr "Animal") [Variable (V "x")]]])]

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runIdentity (runProverT (loadKB sentences >> theoremKB (Predicate "Kills" [Function (Fn "Jack") [], Function (Fn "Tuna") []])))))

proof1 :: (Bool, SetOfSupport V Pr AtomicFunction {-[ImplicativeNormalForm V Pr AtomicFunction]-})
proof1 = ( False
         , [(INF [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[])] )

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runIdentity (runProverT (loadKB sentences >> theoremKB (Predicate "Kills" [Function (Fn "Curiosity") [], Function (Fn "Tuna") []])))))

proof2 :: (Bool, SetOfSupport V Pr AtomicFunction)
proof2 = ( True
         , [(INF [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "y2")]] [],[]),(INF [] [],[])])

testProof :: MonadIO m => String -> (Sentence V Pr AtomicFunction, Bool, [ImplicativeNormalForm V Pr AtomicFunction]) -> ProverT V Pr AtomicFunction m ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT V Pr AtomicFunction m [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
loadCmd = loadKB sentences

sentences :: [Sentence V Pr AtomicFunction]
sentences = [Quantifier ExistsCh ["x"] (Connective (Predicate "Dog" [Variable "x"]) And (Predicate "Owns" [Function "Jack" [], Variable "x"])),
             Quantifier ForAll ["x"] (Connective (Connective (Quantifier ExistsCh ["y"] (Predicate "Dog" [Variable "y"])) And
                                                             (Predicate "Owns" [Variable "x", Variable "y"])) Imply
                                                 (Predicate "AnimalLover" [Variable "x"])),

             Quantifier ForAll ["x"] (Connective (Predicate "AnimalLover" [Variable "x"]) Imply
                                                 (Quantifier ForAll ["y"] (Connective (Predicate "Animal" [Variable "y"]) Imply
                                                                                      (Not (Predicate "Kills" [Variable "x", Variable "y"]))))),

             Connective (Predicate "Kills" [Function "Jack" [], Function "Tuna" []]) Or
                        (Predicate "Kills" [Function "Curiosity" [], Function "Tuna" []]),
             Predicate "Cat" [Function "Tuna" []],
             Quantifier ForAll ["x"] (Connective (Predicate "Cat" [Variable "x"]) Imply (Predicate "Animal" [Variable "x"]))]

-- Ugly Printing

--deriving instance (Show v, Show p, Show f) => Show (Sentence v p f)
deriving instance (Show v, Show p, Show f) => Show (ImplicativeNormalForm v p f)
deriving instance (Show v, Show p, Show f) => Show (NormalSentence v p f)
--deriving instance (Show v, Show f) => Show (Term v f)
--deriving instance Show Quantifier
--deriving instance Show Connective
