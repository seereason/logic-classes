-- | Formula instance used in the unit tests.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, TypeFamilies #-}
module Data.Logic.Instances.Test
    ( V(..)
    , Predicate
    , QFormula(..)
    , Term(..)
    , Function(..)
    , Formula, SkAtom, SkTerm
    , TFormula, TAtom, TTerm -- deprecated
    ) where

import Data.Char (isDigit)
import Data.SafeCopy (base, deriveSafeCopy)
import FOL (V(V), Predicate, FOL(..), Term(..), Quant(..), QFormula(..))
import Formulas (BinOp(..))
import Skolem (Function(..), Formula, SkTerm, SkAtom)

next :: String -> String
next s =
    case break (not . isDigit) (reverse s) of
      (_, "") -> "x"
      ("", nondigits) -> nondigits ++ "2"
      (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)

type TFormula = Formula
type TAtom = SkAtom
type TTerm = SkTerm

$(deriveSafeCopy 1 'base ''BinOp)
$(deriveSafeCopy 1 'base ''Quant)
$(deriveSafeCopy 1 'base ''Predicate)
$(deriveSafeCopy 1 'base ''Term)
$(deriveSafeCopy 1 'base ''FOL)
$(deriveSafeCopy 1 'base ''QFormula)
