{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.Propositional
    ( Formula(..)
    ) where

import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity(..), topFixity)
import Data.Logic.Classes.Propositional (PropositionalFormula(..), prettyPropositional, fixityPropositional, foldAtomsPropositional, mapAtomsPropositional)

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

instance Negatable (Formula atom) where
    negatePrivate T = F
    negatePrivate F = T
    negatePrivate x = Not x
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Constants (Formula a) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance Combinable (Formula a) where
    a .<=>. b = Iff a b
    a .=>. b = Imp a b
    a .|. b = Or a b
    a .&. b = And a b

instance (Pretty atom, HasFixity atom, Ord atom) => C.Formula (Formula atom) atom where
    atomic = Atom
    foldAtoms = foldAtomsPropositional
    mapAtoms = mapAtomsPropositional

instance (Combinable (Formula atom), Pretty atom, HasFixity atom, Ord atom) => PropositionalFormula (Formula atom) atom where
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

instance (HasFixity atom, Pretty atom, Ord atom) => Literal (Formula atom) atom where
    foldLiteral neg tf at formula =
        case formula of
          T -> tf True
          F -> tf False
          Not f -> neg f
          Atom x -> at x
          _ -> error ("Unexpected literal " ++ show (pretty formula))

instance (Pretty atom, HasFixity atom, Ord atom) => Pretty (Formula atom) where
    pretty = prettyPropositional pretty topFixity

instance (Pretty atom, HasFixity atom, Ord atom) => HasFixity (Formula atom) where
    fixity = fixityPropositional
