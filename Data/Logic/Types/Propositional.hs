{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Logic.Types.Propositional where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..), asBool)
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Propositional (PropositionalFormula(..))

-- | The range of a formula is {True, False} when it has no free variables.
data Formula atom
    = Combine (Combination (Formula atom))
    | Atom atom
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Data,Typeable)

instance Negatable (Formula atom) where
    negatePrivate x = Combine ((:~:) x)
    foldNegation normal inverted (Combine ((:~:) x)) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (Constants atom, Ord atom) => Combinable (Formula atom) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance Constants atom => Constants (Formula atom) where
    fromBool = Atom . fromBool

instance (Constants atom, Ord atom) => PropositionalFormula (Formula atom) atom where
    atomic a = Atom a
    foldPropositional co tf at formula =
        case formula of
          Combine x -> co x
          Atom x -> maybe (at x) tf (asBool x)
