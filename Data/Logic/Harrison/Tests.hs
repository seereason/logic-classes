{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings #-}
module Data.Logic.Harrison.Tests where

import Control.Applicative.Error (Failing(..))
import Data.Char (isDigit)
import Data.Generics (Data, Typeable)
import Data.Logic.Classes (Term(..), Pretty(..), Skolem(..), Variable)
import Data.Logic.Harrison.Unif
import Data.String (IsString(..))
import FOL (Term(Var, FApply))
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

{-
instance Show AtomicFunction where
    show (Fn s) = show s
    show (Skolem n) = "(toSkolem " ++ show n ++ ")"
-}

instance Pretty AtomicFunction where
    pretty (Fn s) = text s
    pretty (Skolem n) = text ("sK" ++ show n)

-- | The range of a term is an element of a set.
{-
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Read,Show,Data,Typeable)
-}

instance (Ord v, Variable v, Data v, Eq f, Skolem f, Data f) => IsTerm (Term v f) v f where
    vt = Var
    fApp = FunApp
    foldTerm vf fn (Var v) = vf v
    foldTerm vf fn (FApply f ts) = fn f ts
    zipTerms v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FApply f1 ts1, FApply f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing

tests =
    TestList
    [ TestCase (assertEqual "unify 1"
                (Success [(fApp "f" [fApp "f" [var "z"],fApp "g" [var "y"]],
                           fApp "f" [fApp "f" [var "z"],fApp "g" [var "y"]])])
                (unifyAndApply [( fApp "f" [var "x", fApp "g" [var "y"]] :: Term V AtomicFunction
                                 , fApp "f" [fApp "f" [var "z"], var "w"])]))
    , TestCase (assertEqual "unify 2"
                (Success [(fApp "f" [var "y",var "y"],fApp "f" [var "y",var "y"])])
                (unifyAndApply [( fApp "f" [var "x", var "y"] :: Term V AtomicFunction
                                  , fApp "f" [var "y", var "x"] )]))
    , TestCase (assertEqual "unify 3"
                (Failure ["cyclic"])
                (unifyAndApply [( fApp "f" [var "x", fApp "g" [var "y"]]  :: Term V AtomicFunction
                                  , fApp "f" [var "x", var "y"] )]))
    ]
