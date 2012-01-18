{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.Propositional
    ( Formula(..)
    ) where

import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Propositional (PropositionalFormula(..))

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

instance (Combinable (Formula atom), Ord atom) => PropositionalFormula (Formula atom) atom where
    -- The atom type for this formula is the same as its first type parameter.
    atomic = Atom
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
