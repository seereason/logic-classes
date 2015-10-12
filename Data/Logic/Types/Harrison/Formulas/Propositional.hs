{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.Propositional
    ( Formula(..)
    ) where

import Data.Logic.Classes.Constants (HasBoolean(..))
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), topFixity)
import Data.Logic.Classes.Propositional (IsPropositional(..), prettyPropositional, fixityPropositional, overatomsPropositional, onatomsPropositional)

data Formula a
    = F
    | T
    | Atom a
    | Not (Formula a)
    | And (Formula a) (Formula a)
    | Or (Formula a) (Formula a)
    | Imp (Formula a) (Formula a)
    | Iff (Formula a) (Formula a)
    deriving (Eq, Ord)

instance IsNegatable (Formula atom) where
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

instance IsCombinable (Formula a) where
    a .<=>. b = Iff a b
    a .=>. b = Imp a b
    a .|. b = Or a b
    a .&. b = And a b

instance (Pretty atom, HasFixity atom, Ord atom) => C.IsFormula (Formula atom) atom where
    atomic = Atom
    overatoms = overatomsPropositional
    onatoms = onatomsPropositional

instance (IsCombinable (Formula atom), Pretty atom, HasFixity atom, Ord atom) => IsPropositional (Formula atom) atom where
    -- The atom type for this formula is the same as its first type parameter.
    foldPropositional co tf at formula =
        case formula of
          T -> tf True
          F -> tf False
          Not f -> co ((:~:) f)
          And f g -> co (BinOp f (:&:) g)
          Or f g -> co (BinOp f (:|:) g)
          Imp f g -> co (BinOp f (:=>:) g)
          Iff f g -> co (BinOp f (:<=>:) g)
          Atom x -> at x

instance (HasFixity atom, Pretty atom, Ord atom) => IsLiteral (Formula atom) atom where
    foldLiteral neg tf at formula =
        case formula of
          T -> tf True
          F -> tf False
          Not f -> neg f
          Atom x -> at x
          _ -> error ("Unexpected literal " ++ show (pPrint formula))

instance (Pretty atom, HasFixity atom, Ord atom) => Pretty (Formula atom) where
    pPrint = prettyPropositional pPrint topFixity

instance (Pretty atom, HasFixity atom, Ord atom) => HasFixity (Formula atom) where
    fixity = fixityPropositional
