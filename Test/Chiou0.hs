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
import Logic.FirstOrder (Skolem(..))
import Logic.Logic (Boolean(..))
import Logic.NormalForm (disjunctiveNormalForm)
import Test.HUnit

newtype V = V String deriving (Eq, Ord, Show)

instance IsString V where
    fromString = V

-- |A newtype for the Primitive Predicate parameter.
data Pr
    = Pr String
    | T
    | F
    deriving (Eq, Ord, Show)

instance IsString Pr where
    fromString = Pr

instance Boolean Pr where
    fromBool True = T
    fromBool False = F

data AtomicFunction
    = Fn String
    | Skolem Int
    deriving (Eq, Ord, Show)

instance Skolem AtomicFunction where
    toSkolem = Skolem
    fromSkolem (Skolem n) = Just n
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString = Fn

tests :: Test
tests = TestLabel "Chiou0" $ TestList [loadTest, distributeTest, proofTest1, proofTest2]

{-
main :: IO ()
main = runTestTT (TestList [loadTest, distributeTest, proofTest1, proofTest2]) >>= \ counts ->
       exitWith (if errors counts /= 0 || failures counts /= 0 then ExitFailure 1 else ExitSuccess)
-}

loadTest :: Test
loadTest =
    TestCase (assertEqual "Chiuo0 - loadKB test" expected (runIdentity (runProverT (loadKB sentences))))
    where
      expected :: [(Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])]
      expected = [(Nothing,[INF [] [NFPredicate (Pr "Dog") [Function (Skolem 1) []]],INF [] [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Function (Skolem 1) []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Variable (V "x"),Variable (V "y")]] [NFPredicate (Pr "AnimalLover") [Variable (V "x")]]]),
                  (Nothing,[INF [NFPredicate (Pr "AnimalLover") [Variable (V "x")],NFPredicate (Pr "Animal") [Variable (V "y")],NFPredicate (Pr "Kills") [Variable (V "x"),Variable (V "y")]] []]),
                  (Nothing,[INF [] [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []],NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [] [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]]]),
                  (Nothing,[INF [NFPredicate (Pr "Cat") [Variable (V "x")]] [NFPredicate (Pr "Animal") [Variable (V "x")]]])]
      
{-
testLoad :: Monad m => [(Sentence V Pr AtomicFunction, Maybe [ImplicativeNormalForm V Pr AtomicFunction])] -> ProverT V Pr AtomicFunction m ()
testLoad ss =
    if actual /= expected
    then error ("Expected:\n " ++ show expected ++ "\nActual:\n " ++ show actual)
    else return () -- liftIO (putStrLn "testLoad ok")
    where
      actual :: [Maybe [ImplicativeNormalForm V Pr AtomicFunction]]
      actual = map snd ss
-}

distributeTest :: Test
distributeTest =
    TestCase
    (assertEqual "Chiuo0 - distribute test" 

     (Connective
      (Connective 
       (Connective (Not (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")])) Or (Connective (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")])) Or (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])))
       And
       (Connective (Not (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")])) Or (Connective (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])) Or (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))))
      And 
      (Connective
       (Connective (Connective (Connective (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]) Or (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])) Or (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")]))
        And
        (Connective (Connective (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])) Or (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])) Or (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")])))
       And
       (Connective
        (Connective (Connective (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]) Or (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))) Or (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")]))
        And
        (Connective (Connective (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])) Or (Not (Predicate (Pr "f") [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))) Or (Predicate (Pr "q") [Variable (V "x"),Variable (V "y")])))))

     (disjunctiveNormalForm
      (Connective
       (Connective
        (Not (Predicate "q" [Variable (V "x"),Variable (V "y")]))
        Or
        (Connective
         (Connective
          (Not (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))
          Or
          (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")]))
         And
         (Connective
          (Not (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")]))
          Or
          (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))))
       And
       (Connective
        (Connective
         (Connective
          (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")])
          And
          (Not (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])))
         Or
         (Connective
          (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "y")])
          And
          (Not (Predicate "f" [Function (toSkolem 1) [Variable (V "x"),Variable (V "x"),Variable (V "y"),Variable (V "z")],Variable (V "x")]))))
        Or
        (Predicate "q" [Variable (V "x"),Variable (V "y")])) :: Sentence V Pr AtomicFunction)))

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runIdentity (runProverT (loadKB sentences >> theoremKB (Predicate "Kills" [Function (Fn "Jack") [], Function (Fn "Tuna") []])))))

proof1 :: (Bool, SetOfSupport V Pr AtomicFunction {-[ImplicativeNormalForm V Pr AtomicFunction]-})
proof1 = ( False
         , [(INF [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Curiosity") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Curiosity") [],Variable (V "y")]] [],[])] )

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runIdentity (runProverT (loadKB sentences >> theoremKB (Predicate "Kills" [Function (Fn "Curiosity") [], Function (Fn "Tuna") []])))))

proof2 :: (Bool, SetOfSupport V Pr AtomicFunction)
proof2 = ( True
         , [(INF [NFPredicate (Pr "Kills") [Function (Fn "Curiosity") [],Function (Fn "Tuna") []]] [],[]),(INF [] [NFPredicate (Pr "Kills") [Function (Fn "Jack") [],Function (Fn "Tuna") []]],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "AnimalLover") [Function (Fn "Jack") []]] [],[]),(INF [NFPredicate (Pr "Animal") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []],NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")],NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")],NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Cat") [Function (Fn "Tuna") []]] [],[]),(INF [NFPredicate (Pr "Owns") [Function (Fn "Jack") [],Variable (V "y")]] [],[]),(INF [NFPredicate (Pr "Dog") [Variable (V "z")]] [],[]),(INF [] [],[])])

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
