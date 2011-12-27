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
    (.~.) = Not
    negated (Not _) = True
    negated _ = False

instance Constants (Formula a) where
    fromBool True = T
    fromBool False = F

instance Ord a => Combinable (Formula a) where
    a .<=>. b = Iff a b
    a .=>. b = Imp a b
    a .|. b = Or a b
    a .&. b = And a b

instance Combinable (Formula atom) => PropositionalFormula (Formula atom) atom where
    -- The atom type for this formula is the same as its first type parameter.
    atomic = Atom
    foldPropositional c a formula =
        case formula of
          T -> c TRUE
          F -> c FALSE
          Atom x -> a x
          Not f -> c ((:~:) f)
          And f g -> c (BinOp f (:&:) g)
          Or f g -> c (BinOp f (:|:) g)
          Imp f g -> c (BinOp f (:=>:) g)
          Iff f g -> c (BinOp f (:<=>:) g)
