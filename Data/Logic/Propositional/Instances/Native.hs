{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses #-}
module Data.Logic.Propositional.Instances.Native where

import Data.Generics (Data, Typeable)
import Data.Logic.Logic
import Data.Logic.Propositional.Formula

-- | The range of a formula is {True, False} when it has no free variables.
data Formula atom
    = Combine (Combine (Formula atom))
    | Atom atom
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

instance Negatable (Formula atom) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False

instance Ord atom => Logic (Formula atom) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance Boolean atom => Boolean (Formula atom) where
    fromBool = Atom . fromBool

instance (Boolean atom, Ord atom) => PropositionalFormula (Formula atom) atom where
    atomic a = Atom a
    foldF0 c a formula =
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
