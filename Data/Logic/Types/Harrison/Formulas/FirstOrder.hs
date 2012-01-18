{-# LANGUAGE FlexibleContexts, FlexibleInstances, DeriveDataTypeable, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Formulas.FirstOrder
    ( Formula(..)
    ) where

--import Data.Char (isDigit)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), prettyFirstOrder)
import qualified Data.Logic.Classes.FirstOrder as C
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity)
import Data.Logic.Classes.Variable (Variable(..))
import qualified Data.Set as Set
import Text.PrettyPrint (text)

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

instance Pretty String where
    pretty = text

instance Variable String where
    variant x vars = if Set.member x vars then variant (x ++ "'") vars else x
    prefix p x = p ++ x
    prettyVariable = text
{-
instance Variable String where
    variant v vs =
        if Set.member v vs then variant (next v) (Set.insert v vs) else v
        where
          next :: String -> String
          next s =
              case break (not . isDigit) (reverse s) of
                (_, "") -> "x"
                ("", nondigits) -> nondigits ++ "2"
                (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)
-}

instance (Constants a, Pretty a, HasFixity a) => FirstOrderFormula (Formula a) a String where
    atomic = Atom
    for_all = Forall
    exists = Exists
    foldFirstOrder qu co tf at fm =
        case fm of
          F -> tf False
          T -> tf True
          Atom atom -> at atom
          Not fm' -> co ((:~:) fm')
          And fm1 fm2 -> co (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> co (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> co (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> co (BinOp fm1 (:<=>:) fm2)
          Forall v fm' -> qu C.Forall v fm'
          Exists v fm' -> qu C.Exists v fm'

instance (Constants a, Pretty a, HasFixity a) => Pretty (Formula a) where
    pretty = prettyFirstOrder (const pretty) pretty 0