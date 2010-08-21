{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Test.Types
    ( -- * Formula parameter types
      V(..)
    , Pr(..)
    , AtomicFunction(..)
      -- * Formula and term aliases
    -- , Formula
    -- , ATerm
      -- * Test case types
    , TestFormula(..)
    , Expected(..)
    , TestProof(..)
    , ProofExpected(..)
    ) where

import Data.Char (isDigit)
import Data.Generics (Data, Typeable)
import qualified Data.Set as S
import Data.String (IsString(fromString))
--import Logic.Chiou.FirstOrderLogic (Sentence, CTerm)
--import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalTerm(..))
import Logic.FirstOrder (Skolem(..), Pretty(..), showForm)
import qualified Logic.Instances.Chiou as C
import qualified Logic.Instances.Native as P
import Logic.Logic (Boolean(..))
import Logic.Monad (WithId)
import Logic.Resolution (SetOfSupport)
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

data TestFormula formula
    = TestFormula
      { formula :: formula
      , name :: String
      , expected :: [Expected formula]
      } deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data Expected formula
    = FirstOrderFormula formula
    | SimplifiedForm formula
    | NegationNormalForm formula
    | PrenexNormalForm formula
    | SkolemNormalForm formula
    | SkolemNumbers (S.Set Int)
    -- | ConjunctiveNormalForm formula
    | ClauseNormalForm (S.Set (S.Set formula))
    | TrivialClauses [(Bool, (S.Set formula))]
    | ConvertToChiou formula
    -- | SatChiou (Maybe Bool, [C.ImplicativeNormalForm V Pr AtomicFunction])
    | SatPropLogic Bool
    deriving (Data, Typeable)

data TestProof inf formula term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [formula])
      , conjecture :: formula
      , proofExpected :: [ProofExpected inf v term]
      } deriving (Data, Typeable)

{-
type Formula = P.Formula V Pr AtomicFunction
type ATerm = P.PTerm V AtomicFunction

instance Boolean Formula where
    fromBool = undefined

instance (Show V, Show Pr, Show AtomicFunction) => Show Formula where
    show = showForm

data TestFormula
    = TestFormula
      { formula :: Formula
      , name :: String
      , expected :: [Expected]
      } deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data Expected
    = ClausalNormalForm [[Formula]]
    | DisjunctiveNormalForm Formula
    | PrenexNormalForm Formula
    | NegationNormalForm Formula
    | SkolemNormalForm Formula
    | SkolemNumbers (S.Set Int)
    | FirstOrderFormula Formula
    | ConvertToChiou Formula
    | SatChiou (Maybe Bool, [P.ImplicativeNormalForm V Pr AtomicFunction])
    | SatPropLogic Bool
    deriving (Data, Typeable)

data TestProof
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [Formula])
      , conjecture :: Formula
      , proofExpected :: [ProofExpected]
      } deriving (Data, Typeable)
-}

data ProofExpected inf v term
    = -- ChiouResult (Bool, SetOfSupport (C.ImplicativeNormalForm V Pr AtomicFunction) V (C.CTerm V AtomicFunction))
      ChiouResult (Bool, SetOfSupport inf v term{- (C.ImplicativeNormalForm V Pr AtomicFunction) V (C.CTerm V AtomicFunction) -})
    | ChiouKB [WithId inf{- (C.ImplicativeNormalForm V Pr AtomicFunction) -}]
    deriving (Data, Typeable)

-- This allows you to use an expression that returns the Doc type in a
-- unit test, such as prettyForm 0.
instance Eq Doc where
    a == b = show a == show b
