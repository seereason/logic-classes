{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}

module Chiou0 where

import Common ({-instance Atom MyAtom MyTerm V-})
import Control.Monad.Trans (MonadIO, liftIO)
import Data.Logic.Instances.Test (V(..), Function(..), TFormula, TTerm)
import Data.Logic.KnowledgeBase (ProverT, runProver', Proof(..), ProofResult(..), loadKB, theoremKB {-, askKB, showKB-})
import Data.Logic.Normal.Implicative (ImplicativeForm(INF), makeINF')
import Data.Logic.Resolution (SetOfSupport)
import Data.Map (fromList)
import FOL (exists, for_all, IsTerm(..), pApp)
import Formulas (IsCombinable(..), IsNegatable(..), (.~.))
import qualified Data.Set as S
import Pretty (assertEqual')
import Prop (Literal, Marked)
import Skolem (HasSkolem(..), SkolemT)
import Test.HUnit

tests :: Test
tests = TestLabel "Test.Chiou0" $ TestList [loadTest, proofTest1, proofTest2]

loadTest :: Test
loadTest =
    let label = "Chiuo0 - loadKB test" in
    TestLabel label (TestCase (assertEqual' label expected (runProver' Nothing (loadKB sentences))))
    where
      expected :: [Proof (Marked Literal TFormula)]
      expected = [Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Dog") [fApp (toSkolem "x") []])]),
                                             makeINF' ([]) ([(pApp ("Owns") [fApp ("Jack") [],fApp (toSkolem "x") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [vt ("x"),vt ("y")])]) ([(pApp ("AnimalLover") [vt ("x")])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Animal") [vt ("y")]),(pApp ("AnimalLover") [vt ("x")]),(pApp ("Kills") [vt ("x"),vt ("y")])]) ([])]),
                  Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []]),(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([]) ([(pApp ("Cat") [fApp ("Tuna") []])])]),
                  Proof Invalid (S.fromList [makeINF' ([(pApp ("Cat") [vt ("x")])]) ([(pApp ("Animal") [vt ("x")])])])]

proofTest1 :: Test
proofTest1 = let label = "Chiuo0 - proof test 1" in
             TestLabel label (TestCase (assertEqual' label proof1 (runProver' Nothing (loadKB sentences >> theoremKB (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []] :: TFormula)))))

inf' :: (IsNegatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
inf' l1 l2 = INF (S.fromList l1) (S.fromList l2)

proof1 :: (Bool, SetOfSupport (Marked Literal TFormula) V TTerm)
proof1 = (False,
          (S.fromList
           [(makeINF' ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([]) ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("AnimalLover") [fApp ("Curiosity") []])]) ([]),fromList []),
            (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList []),
            (makeINF' ([(pApp ("Owns") [fApp ("Curiosity") [],vt ("y")])]) ([]),fromList [])]))

proofTest2 :: Test
proofTest2 = let label = "Chiuo0 - proof test 2" in
             TestLabel label (TestCase (assertEqual' label proof2 (runProver' Nothing (loadKB sentences >> theoremKB conjecture))))
    where
      conjecture :: TFormula
      conjecture = (pApp "Kills" [fApp "Curiosity" [], fApp (Fn "Tuna") []])

proof2 :: (Bool, SetOfSupport (Marked Literal TFormula) V TTerm)
proof2 = (True,
          S.fromList
          [(makeINF' ([]) ([]),fromList []),
           (makeINF' ([]) ([(pApp ("Kills") [fApp ("Jack") [],fApp ("Tuna") []])]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Animal") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("AnimalLover") [fApp ("Jack") []]),(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Cat") [fApp ("Tuna") []]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Dog") [vt ("y'")]),(pApp ("Owns") [fApp ("Jack") [],vt ("y")])]) ([]),fromList []),
           (makeINF' ([(pApp ("Kills") [fApp ("Curiosity") [],fApp ("Tuna") []])]) ([]),fromList [])])

testProof :: MonadIO m => String -> (TFormula, Bool, (S.Set (ImplicativeForm (Marked Literal TFormula)))) -> ProverT (ImplicativeForm (Marked Literal TFormula)) (SkolemT m) ()
testProof label (question, expectedAnswer, expectedProof) =
    theoremKB question >>= \ (actualFlag, actualProof) ->
    let actual' = (actualFlag, S.map fst actualProof) in
    if actual' /= (expectedAnswer, expectedProof)
    then error ("\n Expected:\n  " ++ show (expectedAnswer, expectedProof) ++
                "\n Actual:\n  " ++ show actual')
    else liftIO (putStrLn (label ++ " ok"))

loadCmd :: Monad m => ProverT (ImplicativeForm (Marked Literal TFormula)) (SkolemT m) [Proof (Marked Literal TFormula)]
loadCmd = loadKB sentences

-- instance IsAtom (Predicate Pr (PTerm V Function))

sentences :: [TFormula]
sentences = [exists "x" ((pApp "Dog" [vt "x"]) .&. (pApp "Owns" [fApp "Jack" [], vt "x"])),
             for_all "x" (((exists "y" (pApp "Dog" [vt "y"])) .&. (pApp "Owns" [vt "x", vt "y"])) .=>. (pApp "AnimalLover" [vt "x"])),
             for_all "x" ((pApp "AnimalLover" [vt "x"]) .=>. (for_all "y" ((pApp "Animal" [vt "y"]) .=>. ((.~.) (pApp "Kills" [vt "x", vt "y"]))))),
             (pApp "Kills" [fApp "Jack" [], fApp "Tuna" []]) .|. (pApp "Kills" [fApp "Curiosity" [], fApp "Tuna" []]),
             pApp "Cat" [fApp "Tuna" []],
             for_all "x" ((pApp "Cat" [vt "x"]) .=>. (pApp "Animal" [vt "x"]))]
