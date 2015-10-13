{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.FirstOrder
    ( Formula(..)
    ) where

--import Data.Char (isDigit)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(..))
import Data.Logic.Classes.FirstOrder (IsQuantified(..), prettyFirstOrder, overatomsFirstOrder, onatomsFirstOrder)
import qualified Data.Logic.Classes.FirstOrder as C
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity)
import Data.Logic.Types.Common ({- instance Variable String -})

data Formula a
    = F
    | T
    | Atom a
    | Not (Formula a)
    | And (Formula a) (Formula a)
    | Or (Formula a) (Formula a)
    | Imp (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)
    | Forall String (Formula a)
    | Exists String (Formula a)
    deriving (Eq, Ord)

instance Ord atom => IsNegatable (Formula atom) where
    naiveNegate T = F
    naiveNegate F = T
    naiveNegate x = Not x
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance HasBoolean (Formula a) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance Ord a => IsCombinable (Formula a) where
    a .<=>. b = Iff a b
    a .=>. b = Imp a b
    a .|. b = Or a b
    a .&. b = And a b

instance (HasFixity (Formula a), HasBoolean a, Pretty a, Ord a, HasFixity a) => C.IsFormula (Formula a) a where
    atomic = Atom
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder
    prettyFormula = undefined

instance (C.IsFormula (Formula a) a, HasBoolean a, Pretty a, HasFixity a, Ord a) => IsQuantified (Formula a) a String where
    quant (C.:!:) = Forall 
    quant (C.:?:) = Exists
    foldQuantified qu co tf at fm =
        case fm of
          F -> tf False
          T -> tf True
          Atom atom -> at atom
          Not fm' -> co ((:~:) fm')
          And fm1 fm2 -> co (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> co (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> co (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> co (BinOp fm1 (:<=>:) fm2)
          Forall v fm' -> qu (C.:!:) v fm'
          Exists v fm' -> qu (C.:?:) v fm'

instance (IsQuantified (Formula a) a String) => Pretty (Formula a) where
    pPrint = prettyFirstOrder (const pPrint) pPrint 0
