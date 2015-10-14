{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
module Data.Logic.Types.Propositional
#if 1
    ( module Prop
    ) where

import Prop
#else
    where

import Data.Generics (Data, Typeable)
--import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
--import Data.Logic.Classes.Constants (HasBoolean(..), asBool)
import Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (IsLiteral(..))
--import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), rootFixity)
import Data.Logic.Classes.Propositional (IsPropositional(..){-, prettyPropositional, fixityPropositional, overatomsPropositional, onatomsPropositional-})

-- | The range of a formula is {True, False} when it has no free variables.
data Formula atom
    = Combine (Combination (Formula atom))
    | Atom atom
    | T
    | F
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Data,Typeable)

instance Ord atom => IsNegatable (Formula atom) where
    naiveNegate x = Combine ((:~:) x)
    foldNegation normal inverted (Combine ((:~:) x)) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (Ord atom) => IsCombinable (Formula atom) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)


instance HasBoolean (Formula atom) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing
{-
instance (Pretty atom, HasFixity atom, Ord atom) => C.IsFormula (Formula atom) atom where
    atomic = Atom
    overatoms = overatomsPropositional
    onatoms = onatomsPropositional
    prettyFormula = error "prettyFormula is not in atp-haskell"
-}
instance (Pretty atom, HasFixity atom, Ord atom) => IsLiteral (Formula atom) atom where
    foldLiteral neg tf at formula =
        case formula of
          Combine ((:~:) p) -> neg p
          Combine _ -> error ("Unexpected literal: " ++ show (pPrint formula))
          Atom x -> at x
          T -> tf True
          F -> tf False

instance (C.IsFormula (Formula atom) atom, Pretty atom, HasFixity atom, Ord atom) => IsPropositional (Formula atom) atom where
    foldPropositional co tf at formula =
        case formula of
          Combine x -> co x
          Atom x -> at x
          T -> tf True
          F -> tf False

{-
instance (Pretty atom, HasFixity atom, Ord atom) => Pretty (Formula atom) where
    pPrint = prettyPropositional pPrint rootFixity

instance (Pretty atom, HasFixity atom, Ord atom) => HasFixity (Formula atom) where
    fixity = fixityPropositional
-}
#endif
