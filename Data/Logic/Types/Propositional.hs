{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Logic.Types.Propositional where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Combine (Combinable(..), Combine(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Propositional (PropositionalFormula(..))

-- | The range of a formula is {True, False} when it has no free variables.
data Formula atom
    = Combine (Combine (Formula atom))
    | Atom atom
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Data,Typeable)

instance Negatable (Formula atom) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False

instance (Constants atom, Ord atom) => Combinable (Formula atom) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance Constants atom => Constants (Formula atom) where
    fromBool = Atom . fromBool

instance (Constants atom, Ord atom) => PropositionalFormula (Formula atom) atom where
    atomic a = Atom a
    foldPropositional c a formula =
        case formula of
          Combine x -> c x
          Atom x -> a x
{-
    asBool (Atom x) =
        if x == fromBool True
        then Just True
        else if x == fromBool False
             then Just False
             else Nothing
    asBool (Combine _) = Nothing
-}
