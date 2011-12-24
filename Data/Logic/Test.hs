-- |Types to use for creating test cases.  These are used in the Logic
-- package test cases, and are exported for use in its clients.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, RankNTypes, ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Test
    ( -- * Formula parameter types
      V(..)
    , Pr(..)
    , AtomicFunction(..)
    , TFormula
    , TTerm
    , prettyV
    , prettyP
    , prettyF
      -- * Test case types
    , TestFormula(..)
    , Expected(..)
    , doTest
    , TestProof(..)
    , ProofExpected(..)
    , doProof
    ) where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Boolean.SatSolver (CNF)
import Data.Char (isDigit)
import Data.Generics (Data, Typeable, listify)
--import Data.Logic.Clause (ClauseNormalFormula(satisfiable))
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(satisfiable))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula, convertFOF)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Variable (Variable(..))
--import qualified Data.Logic.Instances.Chiou as C
import qualified Data.Logic.Types.FirstOrder as P
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Clause (clauseNormalForm, trivial)
import Data.Logic.Normal.Negation (negationNormalForm, simplify)
import Data.Logic.Normal.Prenex (prenexNormalForm)
import Data.Logic.Normal.Implicative (ImplicativeForm)
import Data.Logic.Normal.Skolem (skolemNormalForm, runNormal, runNormal', runNormalT')
import Data.Logic.Classes.Arity (Arity(arity))
import Data.Logic.Resolution (SetOfSupport)
import qualified Data.Set as S
import Data.String (IsString(fromString))

--import PropLogic (PropForm)

import Test.HUnit
import Text.PrettyPrint (Doc, text)

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

prettyV :: V -> Doc
prettyV (V s) = text s

instance Variable V where
    prefix p (V s) = V (p ++ s)
    variant x xs =
        if S.member x xs
        then variant (next x) xs
        else x
        where
          next :: V -> V
          next (V s) = 
              V (case break (not . isDigit) (reverse s) of
                   (_, "") -> "x"
                   ("", nondigits) -> nondigits ++ "2"
                   (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int))
    fromString = V
    prettyVariable (V s) = text s

-- |A newtype for the Primitive Predicate parameter.
data Pr
    = Pr String
    | T
    | F
    | Equals
    deriving (Eq, Ord, Data, Typeable)

instance IsString Pr where
    fromString = Pr

instance Constants Pr where
    fromBool True = T
    fromBool False = F

instance Arity Pr where
    arity (Pr _) = Nothing
    arity T = Just 0
    arity F = Just 0
    arity Equals = Just 2

instance Show Pr where
    show T = "fromBool True"
    show F = "fromBool False"
    show Equals = ".=."
    show (Pr s) = show s            -- Because Pr is an instance of IsString

prettyP :: Pr -> Doc
prettyP T = text "True"
prettyP F = text "False"
prettyP Equals = text ".=."
prettyP (Pr s) = text s

data AtomicFunction
    = Fn String
    | Skolem Int
    deriving (Eq, Ord, Data, Typeable)

instance Skolem AtomicFunction where
    toSkolem = Skolem
    fromSkolem (Skolem n) = Just n
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString = Fn

instance Show AtomicFunction where
    show (Fn s) = show s
    show (Skolem n) = "toSkolem " ++ show n

prettyF :: AtomicFunction -> Doc
prettyF (Fn s) = text s
prettyF (Skolem n) = text ("sK" ++ show n)

type TFormula = P.Formula V Pr AtomicFunction
type TTerm = P.PTerm V AtomicFunction

-- |This allows you to use an expression that returns the Doc type in a
-- unit test, such as prettyFirstOrder.
instance Eq Doc where
    a == b = show a == show b

data TestFormula formula term v p f
    = TestFormula
      { formula :: formula
      , name :: String
      , expected :: [Expected formula term v p f]
      } deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data (FirstOrderFormula formula term v p f) => Expected formula term v p f
    = FirstOrderFormula formula
    | SimplifiedForm formula
    | NegationNormalForm formula
    | PrenexNormalForm formula
    | SkolemNormalForm formula
    | SkolemNumbers (S.Set Int)
    | ClauseNormalForm (S.Set (S.Set formula))
    | TrivialClauses [(Bool, (S.Set formula))]
    | ConvertToChiou formula
    | ChiouKB1 (Proof formula)
    | PropLogicSat Bool
    | SatSolverCNF CNF
    | SatSolverSat Bool
    deriving (Data, Typeable)

doTest :: (FirstOrderFormula formula term v p f, Literal formula term v p f, Data formula, Show term, Show formula) =>
          TestFormula formula term v p f -> Test
doTest f =
    TestLabel (name f) $ TestList $ 
    map doExpected (expected f)
    where
      doExpected (FirstOrderFormula f') =
          TestCase (assertEqual (name f ++ " original formula") (p f') (p (formula f)))
      doExpected (SimplifiedForm f') =
          TestCase (assertEqual (name f ++ " simplified") (p f') (p (simplify (formula f))))
      doExpected (PrenexNormalForm f') =
          TestCase (assertEqual (name f ++ " prenex normal form") (p f') (p (prenexNormalForm (formula f))))
      doExpected (NegationNormalForm f') =
          TestCase (assertEqual (name f ++ " negation normal form") (p f') (p (negationNormalForm (formula f))))
      doExpected (SkolemNormalForm f') =
          TestCase (assertEqual (name f ++ " skolem normal form") (p f') (p (runNormal (skolemNormalForm (formula f)))))
      doExpected (SkolemNumbers f') =
          TestCase (assertEqual (name f ++ " skolem numbers") f' (skolemSet (runNormal (skolemNormalForm (formula f)))))
      doExpected (ClauseNormalForm fss) =
          TestCase (assertEqual (name f ++ " clause normal form") fss (S.map (S.map p) (runNormal (clauseNormalForm (formula f)))))
      doExpected (TrivialClauses flags) =
          TestCase (assertEqual (name f ++ " trivial clauses") flags (map (\ x -> (trivial x, x)) (S.toList (runNormal (clauseNormalForm (formula f))))))
      doExpected (ConvertToChiou result) =
          TestCase (assertEqual (name f ++ " converted to Chiou") result (convertFOF id id id (formula f)))
      doExpected (ChiouKB1 result) =
          TestCase (assertEqual (name f ++ " Chiou KB") result (runProver' Nothing (loadKB [formula f] >>= return . head)))
      doExpected (PropLogicSat result) =
          TestCase (assertEqual (name f ++ " PropLogic.satisfiable") result (runNormal (plSat (formula f))))
      doExpected (SatSolverCNF result) =
          TestCase (assertEqual (name f ++ " SatSolver CNF") (norm result) (runNormal' (SS.toCNF (formula f))))
      doExpected (SatSolverSat result) =
          TestCase (assertEqual (name f ++ " SatSolver CNF") result (null (runNormalT' (SS.toCNF (formula f) >>= satisfiable))))
      p = id

      norm = map S.toList . S.toList . S.fromList . map S.fromList

skolemSet :: (FirstOrderFormula formula term v p f, Data f, Typeable f, Data formula) => formula -> S.Set Int
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins f s = case fromSkolem f of
                  Just n -> S.insert n s
                  Nothing -> s
      skolemList :: (FirstOrderFormula formula term v p f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

data TestProof formula term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [formula])
      , conjecture :: formula
      , proofExpected :: [ProofExpected formula v term]
      } deriving (Data, Typeable)

data ProofExpected formula v term
    = ChiouResult (Bool, SetOfSupport formula v term)
    | ChiouKB (S.Set (WithId (ImplicativeForm formula)))
    deriving (Data, Typeable)

doProof :: forall formula term v p f. (FirstOrderFormula formula term v p f, Literal formula term v p f, Eq term, Show term, Show v, Show formula) =>
           TestProof formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected (ChiouResult result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover")
                      result
                      (runProver' Nothing (loadKB kb >> theoremKB c)))]]
      doExpected (ChiouKB result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base")
                      result
                      (runProver' Nothing (loadKB kb >> getKB)))]]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula
