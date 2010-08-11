{-# LANGUAGE DeriveDataTypeable, TypeSynonymInstances #-}
module Test.Types
    ( -- * Formula parameter types
      V(..)
    , Pr(..)
    , AtomicFunction(..)
      -- * Formula and term aliases
    , Formula
    , Term
      -- * Test case types
    , TestFormula(..)
    , Expected(..)
    ) where

import Data.Char (isDigit)
import Data.Generics (Data, Typeable)
import Data.String (IsString(fromString))
import Logic.FirstOrder (Skolem(..), Pretty(..), showForm)
import qualified Logic.Instances.Parameterized as P
import Logic.Logic (Boolean(..))
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
type Term = P.Term V AtomicFunction

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
    | PrenexNormalForm Formula
    | NegationNormalForm Formula
    | SkolemNormalForm Formula
    | SatResult Bool
    | FirstOrderFormula Formula
    deriving (Data, Typeable)