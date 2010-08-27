{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, RankNTypes, ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Test.Types
    ( -- * Formula parameter types
      V(..)
    , Pr(..)
    , AtomicFunction(..)
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
import Data.Generics (Data, Typeable, listify, Fixity(..))
import qualified Data.Set as S
import Data.String (IsString(fromString))
import Logic.Clause (Literal, ClauseNormal(satisfiable))
import Logic.FirstOrder (showForm, FirstOrderLogic, convertFOF, Predicate(..), Pretty(..), Skolem(..))
import Logic.Implicative (Implicative(..))
import qualified Logic.Instances.Chiou as C
import qualified Logic.Instances.Native as P
import Logic.Instances.PropLogic (plSat)
import qualified Logic.Instances.SatSolver as SS
import Logic.KnowledgeBase (ProofResult, loadKB, theoremKB, getKB)
import Logic.Logic (Boolean(..))
import Logic.Monad (WithId, runNormal, runProver', runNormal', runNormalT')
import Logic.NormalForm (simplify, negationNormalForm, prenexNormalForm, skolemNormalForm, clauseNormalForm, trivial)
import Logic.Resolution (SetOfSupport)

import Test.HUnit
import Text.PrettyPrint (Doc, (<>), text)

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pretty (V s) = text s

instance Enum V where
    toEnum _ = error "toEnum V"
    fromEnum _ = error "fromEnum V"
    succ (V s) =
        V (case break (not . isDigit) (reverse s) of
             (_, "") -> "x"
             ("", nondigits) -> nondigits ++ "2"
             (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int))
        
-- |A newtype for the Primitive Predicate parameter.
data Pr
    = Pr String
    | T
    | F
    | Equals
    deriving (Eq, Ord, Data, Typeable)

instance IsString Pr where
    fromString = Pr

instance Boolean Pr where
    fromBool True = T
    fromBool False = F

instance Show Pr where
    show T = "fromBool True"
    show F = "fromBool False"
    show (Pr s) = show s            -- Because Pr is an instance of IsString

instance Pretty Pr where
    pretty T = text "True"
    pretty F = text "False"
    pretty (Pr s) = text s

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

instance Pretty AtomicFunction where
    pretty (Fn s) = text s
    pretty (Skolem n) = text ("sK" ++ show n)

-- |This allows you to use an expression that returns the Doc type in a
-- unit test, such as prettyForm 0.
instance Eq Doc where
    a == b = show a == show b

data TestFormula inf formula term v p f
    = TestFormula
      { formula :: formula
      , name :: String
      , expected :: [Expected inf formula term v p f]
      } deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data (Implicative inf formula, FirstOrderLogic formula term v p f) => Expected inf formula term v p f
    = FirstOrderFormula formula
    | SimplifiedForm formula
    | NegationNormalForm formula
    | PrenexNormalForm formula
    | SkolemNormalForm formula
    | SkolemNumbers (S.Set Int)
    | ClauseNormalForm (S.Set (S.Set formula))
    | TrivialClauses [(Bool, (S.Set formula))]
    | ConvertToChiou formula
    | ChiouKB1 (ProofResult, [inf])
    | PropLogicSat Bool
    | SatSolverCNF CNF
    | SatSolverSat Bool
    deriving (Data, Typeable)

doTest :: (Implicative inf formula, FirstOrderLogic formula term v p f, Literal formula, Data formula, Show term) =>
          TestFormula inf formula term v p f -> Test
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
          TestCase (assertEqual (name f ++ " Chiou KB") result (runProver' (loadKB [formula f] >>= return . head)))
      doExpected (PropLogicSat result) =
          TestCase (assertEqual (name f ++ " PropLogic.satisfiable") result (runNormal (plSat (formula f))))
      doExpected (SatSolverCNF result) =
          TestCase (assertEqual (name f ++ " SatSolver CNF") result (runNormal' (SS.toCNF (formula f))))
      doExpected (SatSolverSat result) =
          TestCase (assertEqual (name f ++ " SatSolver CNF") result (null (runNormalT' (SS.toCNF (formula f) >>= satisfiable))))
      p = id -- prettyForm 0

skolemSet :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> S.Set Int
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins f s = case fromSkolem f of
                  Just n -> S.insert n s
                  Nothing -> s
      skolemList :: (FirstOrderLogic formula term v p f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

data TestProof inf formula term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [formula])
      , conjecture :: formula
      , proofExpected :: [ProofExpected inf v term]
      } deriving (Data, Typeable)

data ProofExpected inf v term
    = ChiouResult (Bool, SetOfSupport inf v term)
    | ChiouKB [WithId inf]
    deriving (Data, Typeable)

doProof :: forall inf formula term v p f. (FirstOrderLogic formula term v p f, Implicative inf formula, Show inf, Show term) =>
           TestProof inf formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected (ChiouResult result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover")
                      result
                      (runProver' (loadKB kb >> theoremKB c)))]]
      doExpected (ChiouKB result) =
          [TestLabel (proofName p ++ " with " ++ fst (proofKnowledge p)) . TestList $
           [TestCase (assertEqual (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base")
                      result
                      (runProver' (loadKB kb >> getKB)))]]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula
