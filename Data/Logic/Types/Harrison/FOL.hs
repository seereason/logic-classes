{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Data.Logic.Types.Harrison.FOL
#if 1
    ( module FOL
    ) where

import FOL
#else
    ( TermType(..)
    , FOL(..)
    , Function(..)
    ) where

import Data.Generics (Data, Typeable)
import Data.List (intersperse)
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Apply (HasPredicate(..), IsPredicate)
--import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(fromBool), asBool)
--import Data.Logic.Classes.FirstOrder (foldAtomsFirstOrder, onatomsFirstOrder)
--import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), Fixity(..), Associativity(..))
import Data.Logic.Classes.Skolem (HasSkolem(..))
import Data.Logic.Classes.Term (IsTerm(vt, foldTerm, fApp))
import qualified Data.Logic.Classes.Term as C
--import qualified Data.Logic.Classes.FirstOrder as C
--import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import qualified Data.Logic.Types.Common ({- instance Variable String -})
import Data.String (IsString(fromString))
import Prelude hiding (pred)
import Text.PrettyPrint (text, cat)

-- -------------------------------------------------------------------------
-- Terms.
-- -------------------------------------------------------------------------

data TermType
    = Var String
    | Fn Function [TermType]
    deriving (Eq, Ord)

data FOL = R String [TermType] deriving (Eq, Ord, Show)

instance Show TermType where
    show (Var v) = "vt " ++ show v
    show (Fn f ts) = "fApp " ++ show f ++ " " ++ show ts

instance Pretty TermType where
    pPrint (Var v) = pPrint v
    pPrint (Fn f ts) = cat ([pPrint f, text "("] ++ intersperse (text ", ") (map pPrint ts) ++ [text ")"])

instance HasPredicate FOL String TermType where
    foldPredicate ap (R p ts) = ap p ts
    applyPredicate = R

-- | This is probably dangerous.
instance HasBoolean String where
    fromBool True = "true"
    fromBool False = "false"
    asBool x
        | x == fromBool True = Just True
        | x == fromBool False = Just False
        | True = Nothing

instance HasBoolean FOL where
    fromBool x = R (fromBool x) []
    asBool (R p _) = asBool p

instance IsPredicate String

{-
instance Pretty String where
    pPrint = text

instance FirstOrderFormula (Formula FOL) FOL String where
    -- type C.Term (Formula FOL) = Term
    -- type V (Formula FOL) = String
    -- type Pr (Formula FOL) = String
    -- type Fn (Formula FOL) = String -- ^ Atomic function type

    -- quant C.Exists v fm = H.Exists v fm
    -- quant C.Forall v fm = H.Forall v fm
    for_all = H.Forall
    exists = H.Exists
    atomic = Atom
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
          H.Forall v fm' -> qu C.Forall v fm'
          H.Exists v fm' -> qu C.Exists v fm'
-}

instance Pretty FOL where
    pPrint (R p ts) = cat ([pPrint p, text "("] ++ intersperse (text ", ") (map pPrint ts) ++ [text ")"])

instance Arity String where
    arity _ = Nothing

-- | The Harrison book uses String for atomic function, but we need
-- something a little more type safe because of our Skolem class.
data Function
    = FName String
    | Skolem String
    deriving (Eq, Ord, Data, Typeable, Show)

instance IsString Function where
    fromString = FName

instance Pretty Function where
    pPrint (FName s) = text s
    pPrint (Skolem v) = text ("sK" ++ v)

instance C.Function Function String

instance HasSkolem Function String where
    toSkolem = Skolem
    fromSkolem (Skolem v) = Just v
    fromSkolem _ = Nothing

instance IsTerm TermType String Function where
    -- type V Term = String
    -- type Fn Term = String
    vt = Var
    fApp = Fn
    foldTerm vfn _ (Var x) = vfn x
    foldTerm _ ffn (Fn f ts) = ffn f ts
    zipTerms = undefined

instance HasFixity FOL where
    fixity = const (Fixity 10 InfixN)
#endif
