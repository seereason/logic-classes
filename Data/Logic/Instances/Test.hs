-- | Formula instance used in the unit tests.
{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
module Data.Logic.Instances.Test
    ( V(..)
    , Pr(..)
    , AtomicFunction(..)
    , MyFormula, MyAtom, MyTerm
    , TFormula, TAtom, TTerm -- deprecated
    , prettyV
    , prettyP
    , prettyF
    ) where

import Data.Char (isDigit)
import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Apply (IsPredicate, HasPredicate(..))
import Data.Logic.Classes.Arity (Arity(arity))
import Data.Logic.Classes.Constants (HasBoolean(..), prettyBool)
import Data.Logic.Classes.Equals (HasEquals(isEquals), HasEquality(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint))
import qualified Data.Logic.Classes.Skolem as C (HasSkolem(..))
import Data.Logic.Classes.Term (Function)
import Data.Logic.Classes.Variable (IsVariable(..))
import qualified Data.Logic.Types.FirstOrder as P (Formula, Predicate(..), PTerm)
import Data.Monoid ((<>))
import Data.Set as Set (member)
import Data.String (IsString(fromString))
import Text.PrettyPrint (Doc, text)

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = "fromString " ++ show s

prettyV :: V -> Doc
prettyV (V s) = text s

instance Pretty V where
    pPrint = prettyV

instance IsVariable V where
    prefix p (V s) = V (p ++ s)
    variant x@(V s) xs = if member x xs then variant (V (next s)) xs else x
    prettyVariable (V s) = text s

next :: String -> String
next s =
    case break (not . isDigit) (reverse s) of
      (_, "") -> "x"
      ("", nondigits) -> nondigits ++ "2"
      (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)

-- |A newtype for the Primitive Predicate parameter.
data Pr
    = Pr String
    | T
    | F
    | Equ
    deriving (Eq, Ord, Data, Typeable)

instance IsPredicate Pr

instance HasEquals Pr where
    isEquals Equ = True
    isEquals _ = False

{-
instance HasPredicate (P.Predicate Pr (P.PTerm V AtomicFunction)) Pr (P.PTerm V AtomicFunction) where
    foldPredicate ap (P.Apply p ts) = ap p ts
    foldPredicate ap (P.Equal lhs rhs) = ap Equ [lhs, rhs]
    applyPredicate Equ [lhs, rhs] = P.Equal lhs rhs -- Should this happen?  Or should this be done by applyEquals?
    applyPredicate T [] = P.Apply (fromBool True) []
    applyPredicate F [] = P.Apply (fromBool False) []
    applyPredicate p@(Pr _) ts = P.Apply p ts
    applyPredicate p _ = error ("applyPredicate " ++ show p ++ ": arity error")

instance HasEquality (P.Predicate Pr (P.PTerm V AtomicFunction)) Pr (P.PTerm V AtomicFunction) where
    foldEquals f (P.Equal lhs rhs) = Just (f lhs rhs)
    foldEquals _ _ = Nothing
    applyEquals = P.Equal
-}

instance IsString Pr where
    fromString = Pr

instance HasBoolean Pr where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance Arity Pr where
    arity (Pr _) = Nothing
    arity T = Just 0
    arity F = Just 0
    arity Equ = Just 2

instance Show Pr where
    show T = "fromBool True"
    show F = "fromBool False"
    show Equ = ".=."
    show (Pr s) = show s            -- Because Pr is an instance of IsString

prettyP :: Pr -> Doc
prettyP T = prettyBool True
prettyP F = prettyBool False
prettyP Equ = text ".=."
prettyP (Pr s) = text s

instance Pretty Pr where
    pPrint = prettyP

data AtomicFunction
    = Fn String
    | Skolem V
    deriving (Eq, Ord, Data, Typeable)

instance Function AtomicFunction V

instance C.HasSkolem AtomicFunction V where
    toSkolem = Skolem
    fromSkolem (Skolem v) = Just v
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString = Fn

instance Show AtomicFunction where
    show (Fn s) = show s
    show (Skolem v) = "(toSkolem (" ++ show v ++ "))"

prettyF :: AtomicFunction -> Doc
prettyF (Fn s) = text s
prettyF (Skolem v) = text "sK" <> pPrint v

instance Pretty AtomicFunction where
    pPrint = prettyF

type MyFormula = P.Formula V Pr AtomicFunction
type MyAtom = P.Predicate Pr TTerm
type MyTerm = P.PTerm V AtomicFunction

type TFormula = MyFormula
type TAtom = MyAtom
type TTerm = MyTerm

{-
instance Pretty TFormula where
    pPrint = prettyFirstOrder (const pPrint) pPrint 0
-}
