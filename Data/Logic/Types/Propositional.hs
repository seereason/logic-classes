{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Logic.Types.Propositional where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..), asBool)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity(..), topFixity)
import Data.Logic.Classes.Propositional (PropositionalFormula(..), prettyPropositional, fixityPropositional, foldAtomsPropositional, mapAtomsPropositional)

-- | The range of a formula is {True, False} when it has no free variables.
data Formula atom
    = Combine (Combination (Formula atom))
    | Atom atom
    | T
    | F
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Data,Typeable)

instance Negatable (Formula atom) where
    negatePrivate x = Combine ((:~:) x)
    foldNegation normal inverted (Combine ((:~:) x)) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (Ord atom) => Combinable (Formula atom) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)


instance Constants (Formula atom) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance (Pretty atom, HasFixity atom, Ord atom) => C.Formula (Formula atom) atom where
    atomic = Atom
    foldAtoms = foldAtomsPropositional
    mapAtoms = mapAtomsPropositional

instance (Pretty atom, HasFixity atom, Ord atom) => Literal (Formula atom) atom where
    foldLiteral neg tf at formula =
        case formula of
          Combine ((:~:) p) -> neg p
          Combine _ -> error ("Literal: " ++ show (pretty formula))
          Atom x -> at x
          T -> tf True
          F -> tf False

instance (C.Formula (Formula atom) atom, Pretty atom, HasFixity atom, Ord atom) => PropositionalFormula (Formula atom) atom where
    foldPropositional co tf at formula =
        case formula of
          Combine x -> co x
          Atom x -> at x
          T -> tf True
          F -> tf False

instance (Pretty atom, HasFixity atom, Ord atom) => Pretty (Formula atom) where
    pretty = prettyPropositional pretty topFixity

instance (Pretty atom, HasFixity atom, Ord atom) => HasFixity (Formula atom) where
    fixity = fixityPropositional
