{-# LANGUAGE OverloadedStrings, StandaloneDeriving #-}
{-# OPTIONS -fno-warn-orphans #-}

module Data.Logic.Tests.Chiou0 where

import Control.Monad.Trans (MonadIO, liftIO)
import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Equals (pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Negate (Negatable(..), (.~.))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Harrison.Skolem (SkolemT)
import Data.Logic.KnowledgeBase (ProverT, runProver', Proof(..), ProofResult(..), loadKB, theoremKB {-, askKB, showKB-})
import Data.Logic.Normal.Implicative (ImplicativeForm(INF), makeINF')
import Data.Logic.Resolution (SetOfSupport)
import Data.Logic.Tests.Common (V(..), AtomicFunction(..), TFormula, TTerm, myTest)
import Data.Map (fromList)
import qualified Data.Set as S
import Test.HUnit

tests :: Test
tests = TestLabel "Test.Chiou0" $ TestList [loadTest, proofTest1, proofTest2]

loadTest :: Test
loadTest =
    myTest "Chiuo0 - loadKB test" expected (runProver' Nothing (loadKB sentences))
    where
      expected :: [Proof TFormula]
      expected = [Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Dog") [fApp (toSkolem "x") []])]),
                                             makeINF' ([]) ([(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [vt ("x"),vt ("y")])]) ([(pApp ("AnimalLover") [vt ("x")])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Animal") [vt ("y")]),(pApp ("AnimalLover") [vt ("x")]),(pApp ("Kills") [vt ("x"),vt ("y")])]) ([])]),
                  Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Cat") [fApp ("Tuna") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Cat") [vt ("x")])]) ([(pApp ("Animal") [vt ("x")])])])]

proofTest1 :: Test
proofTest1 = myTest "Chiuo0 - proof test 1" proof1 (runProver' Nothing (loadKB sentences >> theoremKB (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []] :: TFormula)))

inf' :: (Negatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
inf' l1 l2 = INF (S.fromList l1) (S.fromList l2)

proof1 :: (Bool, SetOfSupport TFormula V TTerm)
proof1 = (False,
          (S.fromList
           [(makeINF' ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList [])]))

proofTest2 :: Test
proofTest2 = myTest "Chiuo0 - proof test 2" proof2 (runProver' Nothing (loadKB sentences >> theoremKB conjecture))
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
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Dog") [vt ("y2")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]) ([]),fromList [])])

testProof :: MonadIO m => String -> (TFormula, Bool, (S.Set (ImplicativeForm TFormula))) -> ProverT (ImplicativeForm TFormula) (SkolemT V TTerm m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, S.map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeForm TFormula) (SkolemT V TTerm m) [Proof TFormula]
loadCmd = loadKB sentences

sentences :: [TFormula]
sentences = [exists "x" ((pApp "Dog" [vt "x"]) .&. (pApp "Owns" [fApp "Jack" [], vt "x"])),
             for_all "x" (((exists "y" (pApp "Dog" [vt "y"])) .&. (pApp "Owns" [vt "x", vt "y"])) .=>. (pApp "AnimalLover" [vt "x"])),
             for_all "x" ((pApp "AnimalLover" [vt "x"]) .=>. (for_all "y" ((pApp "Animal" [vt "y"]) .=>. ((.~.) (pApp "Kills" [vt "x", vt "y"]))))),
             (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []]) .|. (pApp "Kills" [fApp "Curiosity" [], fApp "Tuna" []]),
             pApp "Cat" [fApp "Tuna" []],
             for_all "x" ((pApp "Cat" [vt "x"]) .=>. (pApp "Animal" [vt "x"]))]
