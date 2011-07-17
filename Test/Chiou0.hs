{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Test.Chiou0 where

import Control.Monad.Identity (runIdentity)
import Control.Monad.Trans (MonadIO, liftIO)
import Data.Logic.FirstOrder
import Data.Logic.FirstOrder (FirstOrderFormula(..), Term(..), Skolem(..))
import Data.Logic.Instances.Native (Formula, PTerm)
import Data.Logic.KnowledgeBase (ProofResult(..), loadKB, theoremKB {-, askKB, showKB-})
import Data.Logic.Logic (Negatable(..), Logic(..), Boolean(..))
import Data.Logic.Monad (NormalT, runNormal, ProverT, runProver')
import Data.Logic.Normal (ImplicativeNormalForm, makeINF, makeINF')
import Data.Logic.NormalForm (clauseNormalForm)
import Data.Logic.Resolution (SetOfSupport)
import Data.Map (fromList)
import qualified Data.Set as S
import Data.String (IsString(..))
import Test.HUnit
import Test.Types (V(..), Pr(..), AtomicFunction(..), TFormula, TTerm)

tests :: Test
tests = TestLabel "Chiou0" $ TestList [loadTest, proofTest1, proofTest2]

loadTest :: Test
loadTest =
    TestCase (assertEqual "Chiuo0 - loadKB test" expected (runProver' (loadKB id id id sentences)))
    where
      expected :: [(ProofResult, S.Set (ImplicativeNormalForm TFormula))]
      expected = [(Invalid,S.fromList [makeINF' ([]) ([(pApp ("Dog") [fApp (toSkolem 1) []])]),
                                       makeINF' ([]) ([(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem 1) []])])]),
                  (Invalid,S.fromList [makeINF' ([(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [var ("x"),var ("y")])]) ([(pApp ("AnimalLover") [var ("x")])])]),
                  (Invalid,S.fromList [makeINF' ([(pApp ("Animal") [var ("y")]),(pApp ("AnimalLover") [var ("x")]),(pApp ("Kills") [var ("x"),var ("y")])]) ([])]),
                  (Invalid,S.fromList [makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])])]),
                  (Invalid,S.fromList [makeINF' ([]) ([(pApp ("Cat") [fApp ("Tuna") []])])]),
                  (Invalid,S.fromList [makeINF' ([(pApp ("Cat") [var ("x")])]) ([(pApp ("Animal") [var ("x")])])])]

proofTest1 :: Test
proofTest1 = TestCase (assertEqual "Chiuo0 - proof test 1" proof1 (runProver' (loadKB id id id sentences >> theoremKB id id id (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []] :: TFormula))))

inf' l1 l2 = makeINF (S.fromList l1) (S.fromList l2)

proof1 :: (Bool, SetOfSupport TFormula V TTerm)
proof1 = (False,
          (S.fromList
           [(makeINF' ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Owns") [fApp ("Curiosity") [],var ("y")])]) ([]),fromList [])]))

proofTest2 :: Test
proofTest2 = TestCase (assertEqual "Chiuo0 - proof test 2" proof2 (runProver' (loadKB id id id sentences >> theoremKB id id id conjecture)))
    where
      conjecture :: TFormula
      conjecture = (pApp "Kills" [fApp "Curiosity" [], fApp (Fn "Tuna") []])

proof2 :: (Bool, SetOfSupport TFormula V TTerm)
proof2 = (True,
          S.fromList
          [(makeINF' ([]) ([]),fromList []),
           (makeINF' ([]) ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Jack") [],var ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],var ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Jack") [],var ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],var ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Dog") [var ("y2")]),(pApp ("Owns") [fApp ("Jack") [],var ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]) ([]),fromList [])])

testProof :: MonadIO m => String -> (TFormula, Bool, (S.Set (ImplicativeNormalForm TFormula))) -> ProverT (ImplicativeNormalForm TFormula) (NormalT V TTerm m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB id id id question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, S.map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeNormalForm TFormula) (NormalT V TTerm m) [(ProofResult, S.Set (ImplicativeNormalForm TFormula))]
loadCmd = loadKB id id id sentences

sentences :: [TFormula]
sentences = [exists "x" ((pApp "Dog" [var "x"]) .&. (pApp "Owns" [fApp "Jack" [], var "x"])),
             for_all "x" (((exists "y" (pApp "Dog" [var "y"])) .&. (pApp "Owns" [var "x", var "y"])) .=>. (pApp "AnimalLover" [var "x"])),
             for_all "x" ((pApp "AnimalLover" [var "x"]) .=>. (for_all "y" ((pApp "Animal" [var "y"]) .=>. ((.~.) (pApp "Kills" [var "x", var "y"]))))),
             (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []]) .|. (pApp "Kills" [fApp "Curiosity" [], fApp "Tuna" []]),
             pApp "Cat" [fApp "Tuna" []],
             for_all "x" ((pApp "Cat" [var "x"]) .=>. (pApp "Animal" [var "x"]))]
