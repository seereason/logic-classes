{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}
module Data.Logic.Harrison.Tests where

import Control.Applicative.Error (Failing(..))
import Data.Char (isDigit)
import Data.Generics (Data, Typeable)
import Data.String (IsString(..))
import Data.Logic.FirstOrder (Term(..), Pretty(..), Skolem(..), Variable)
import Data.Logic.Harrison.Unif
--import Data.Logic.Instances.Native(PTerm(..))
--import Test.Types
import Test.HUnit
import Text.PrettyPrint (text)

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

instance Pretty V where
    pretty (V s) = text s

instance Variable V where
    next (V s) =
        V (case break (not . isDigit) (reverse s) of
             (_, "") -> "x"
             ("", nondigits) -> nondigits ++ "2"
             (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int))

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

-- | The range of a term is an element of a set.
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Read,Show,Data,Typeable)

instance (Ord v, Variable v, Data v, Eq f, Skolem f, Data f) => Term (PTerm v f) v f where
    foldT vf fn t =
        case t of
          Var v -> vf v
          FunApp f ts -> fn f ts
    zipT v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FunApp f1 ts1, FunApp f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Var
    fApp x args = FunApp x args

tests =
    TestList
    [ TestCase (assertEqual "unify 1"
                (Success [(fApp "f" [fApp "f" [var "z"],fApp "g" [var "y"]],
                           fApp "f" [fApp "f" [var "z"],fApp "g" [var "y"]])])
                (unifyAndApply [( fApp "f" [var "x", fApp "g" [var "y"]] :: PTerm V AtomicFunction
                                 , fApp "f" [fApp "f" [var "z"], var "w"])]))
    , TestCase (assertEqual "unify 2"
                (Success [(fApp "f" [var "y",var "y"],fApp "f" [var "y",var "y"])])
                (unifyAndApply [( fApp "f" [var "x", var "y"] :: PTerm V AtomicFunction
                                  , fApp "f" [var "y", var "x"] )]))
    , TestCase (assertEqual "unify 3"
                (Failure ["cyclic"])
                (unifyAndApply [( fApp "f" [var "x", fApp "g" [var "y"]]  :: PTerm V AtomicFunction
                                  , fApp "f" [var "x", var "y"] )]))
    ]
