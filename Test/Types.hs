{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances #-}
module Test.Types
    ( -- * Formula parameter types
      V(..)
    , Pr(..)
    , AtomicFunction(..)
      -- * Formula and term aliases
    , Formula
    , ATerm
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
import Logic.Chiou.FirstOrderLogic (Sentence)
import Logic.Chiou.Monad (WithId)
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalTerm(..))
import Logic.FirstOrder (Skolem(..), Pretty(..), showForm)
import qualified Logic.Instances.Parameterized as P
import Logic.Logic (Boolean(..))
import Logic.Resolution (SetOfSupport)
import Text.PrettyPrint ((<>), text)

newtype V = V String deriving (Eq, Ord, Show, Data, Typeable)

instance IsString V where
    fromString = V

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
    deriving (Eq, Ord, Show, Data, Typeable)

instance IsString Pr where
    fromString = Pr

instance Boolean Pr where
    fromBool True = T
    fromBool False = F

instance Pretty Pr where
    pretty T = text "True"
    pretty F = text "False"
    pretty (Pr s) = text s

data AtomicFunction
    = Fn String
    | Skolem Int
    deriving (Eq, Ord, Show, Data, Typeable)

instance Skolem AtomicFunction where
    toSkolem = Skolem
    fromSkolem (Skolem n) = Just n
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString = Fn

instance Pretty AtomicFunction where
    pretty (Fn s) = text s
    pretty (Skolem n) = text "Sk" <> text (show n)

type Formula = P.Formula V Pr AtomicFunction
type ATerm = P.PTerm V AtomicFunction

instance Boolean Formula where
    fromBool = undefined

instance Show Formula where
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
    | ConvertToChiou (Sentence V Pr AtomicFunction)
    | SatChiou (Maybe Bool, [ImplicativeNormalForm V Pr AtomicFunction])
    | SatPropLogic Bool
    deriving (Data, Typeable)

data TestProof
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [Sentence V Pr AtomicFunction])
      , conjecture :: Sentence V Pr AtomicFunction
      , proofExpected :: [ProofExpected]
      } deriving (Data, Typeable)

data ProofExpected
    = ChiouResult (Bool, SetOfSupport (ImplicativeNormalForm V Pr AtomicFunction) V (NormalTerm V AtomicFunction))
    | ChiouKB [WithId (ImplicativeNormalForm V Pr AtomicFunction)]
    deriving (Data, Typeable)
