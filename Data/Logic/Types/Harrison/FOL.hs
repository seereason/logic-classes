{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Data.Logic.Types.Harrison.FOL
    ( TermType(..)
    , FOL(..)
    , Function(..)
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Apply (Apply(..), Predicate, showApply)
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool), asBool)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), showFirstOrder)
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(vt, foldTerm, fApp))
import Data.Logic.Classes.Variable (Variable(..))
import qualified Data.Logic.Classes.Term as C
import qualified Data.Logic.Classes.FirstOrder as C
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))
import qualified Data.Logic.Types.Harrison.Formulas.FirstOrder as H
import qualified Data.Set as Set
import Prelude hiding (pred)
import Text.PrettyPrint (text)

-- -------------------------------------------------------------------------
-- Terms.                                                                   
-- -------------------------------------------------------------------------

data TermType
    = Var String
    | Fn Function [TermType]
    deriving (Eq, Ord)

data FOL = R String [TermType] deriving (Eq, Ord, Show)

instance Show TermType where
    show (Var v) = "var " ++ show v
    show (Fn f ts) = "fApp " ++ show f ++ " " ++ show ts

instance Apply FOL String TermType where
    foldApply f tf (R p ts) = maybe (f p ts) tf (asBool p)
    apply' = R

-- | This is probably dangerous.
instance Constants String where
    fromBool True = "true"
    fromBool False = "false"

instance Constants FOL where
    fromBool x = R (fromBool x) []

instance Predicate String

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

instance Arity String where
    arity _ = Nothing

-- | The Harrison book uses String for atomic function, but we need
-- something a little more type safe because of our Skolem class.
data Function
    = FName String
    | Skolem Int
    deriving (Eq, Ord, Data, Typeable, Show)

instance C.Function Function

instance Skolem Function where
    toSkolem = Skolem
    fromSkolem (Skolem n) = Just n
    fromSkolem _ = Nothing

instance Term TermType String Function where
    -- type V Term = String
    -- type Fn Term = String
    vt = Var
    fApp = Fn
    foldTerm vfn _ (Var x) = vfn x
    foldTerm _ ffn (Fn f ts) = ffn f ts
    zipTerms = undefined

instance Variable String where
    variant x vars = if Set.member x vars then variant (x ++ "'") vars else x
    prefix p x = p ++ x
    prettyVariable = text

instance Show (Formula FOL) where
    show = showFirstOrder showApply
