-- | Formula instance used in the unit tests.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, TypeFamilies #-}
module Data.Logic.Instances.Test
    ( V(..)
    , Predicate(..)
    , Formula(..)
    , Term(..)
    , Function(..)
    , MyFormula, MyAtom, MyTerm
    , TFormula, TAtom, TTerm -- deprecated
    ) where

import Data.Char (isDigit)
import Data.SafeCopy (base, deriveSafeCopy)
import FOL (V(V), Predicate(..), FOL(..), Term(..), Quant(..), Formula(..))
import Formulas (BinOp(..))
import Skolem (Function(..), MyFormula, MyTerm, MyAtom)

next :: String -> String
next s =
    case break (not . isDigit) (reverse s) of
      (_, "") -> "x"
      ("", nondigits) -> nondigits ++ "2"
      (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)

{-
instance HasPredicate (P.Predicate Predicate (P.Term V AtomicFunction)) Predicate (P.Term V AtomicFunction) where
    foldPredicate ap (P.Apply p ts) = ap p ts
    foldPredicate ap (P.Equal lhs rhs) = ap Equ [lhs, rhs]
    applyPredicate Equ [lhs, rhs] = P.Equal lhs rhs -- Should this happen?  Or should this be done by applyEquals?
    applyPredicate T [] = P.Apply (fromBool True) []
    applyPredicate F [] = P.Apply (fromBool False) []
    applyPredicate p@(Predicate _) ts = P.Apply p ts
    applyPredicate p _ = error ("applyPredicate " ++ show p ++ ": arity error")

instance HasEquality (P.Predicate Predicate (P.Term V AtomicFunction)) Predicate (P.Term V AtomicFunction) where
    foldEquals f (P.Equal lhs rhs) = Just (f lhs rhs)
    foldEquals _ _ = Nothing
    applyEquals = P.Equal

instance IsString Predicate where
    fromString = Predicate

instance HasBoolean Predicate where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance Arity Predicate where
    arity (Predicate _) = Nothing
    -- arity T = Just 0
    -- arity F = Just 0
    arity Equals = Just 2

instance Show Predicate where
    -- show T = "fromBool True"
    -- show F = "fromBool False"
    show Equals = ".=."
    show (Predicate s) = show s            -- Because Predicate is an instance of IsString

prettyP :: Predicate -> Doc
-- prettyP T = prettyBool True
-- prettyP F = prettyBool False
prettyP Equals = text ".=."
prettyP (Predicate s) = text s

instance Pretty Predicate where
    pPrint = prettyP

data Function
    = Fn String
    | Skolem V
    deriving (Eq, Ord, Data, Typeable)
-}

-- instance IsFunction AtomicFunction V

-- type MyFormula = Formula V Predicate Function
-- type MyAtom = FOL Predicate TTerm
-- type MyTerm = P.Term V Function

type TFormula = MyFormula
type TAtom = MyAtom
type TTerm = MyTerm

{-
instance Pretty TFormula where
    pPrint = prettyFirstOrder (const pPrint) pPrint 0
-}

$(deriveSafeCopy 1 'base ''BinOp)
$(deriveSafeCopy 1 'base ''Quant)
$(deriveSafeCopy 1 'base ''Predicate)
$(deriveSafeCopy 1 'base ''Term)
$(deriveSafeCopy 1 'base ''FOL)
$(deriveSafeCopy 1 'base ''Formula)
