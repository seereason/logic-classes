{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.FirstOrder
    ( Formula(..)
    ) where

import Data.Logic.Classes.Combine (Combinable(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Negate (Negatable(..))

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

instance Negatable (Formula atom) where
    negatePrivate T = F
    negatePrivate F = T
    negatePrivate x = Not x
    foldNegation normal inverted (Not x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Constants (Formula a) where
    fromBool True = T
    fromBool False = F

instance Combinable (Formula a) where
    a .<=>. b = Iff a b
    a .=>. b = Imp a b
    a .|. b = Or a b
    a .&. b = And a b
