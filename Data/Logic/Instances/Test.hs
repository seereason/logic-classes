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
import Data.Logic.ATP.Apply (Predicate)
import Data.Logic.ATP.Equate (FOL(..))
import Data.Logic.ATP.Quantified (Quant(..), QFormula(..))
import Data.Logic.ATP.Prop (BinOp(..))
import Data.Logic.ATP.Skolem (Function(..), Formula, SkTerm, SkAtom)
import Data.Logic.ATP.Term (V(V), Term(..))
import Data.SafeCopy (base, deriveSafeCopy)

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
