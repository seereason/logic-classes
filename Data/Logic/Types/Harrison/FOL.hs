{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Data.Logic.Types.Harrison.FOL
    ( TermType(..)
    , FOL(..)
    ) where

import Data.Logic.Classes.Arity
import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), showFirstOrder)
import Data.Logic.Classes.Term (Term(vt, foldTerm, fApp), Function(variantF))
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
    | Fn String [TermType]
    deriving (Eq, Ord)

data FOL = R String [TermType] deriving (Eq, Ord, Show)

instance Show TermType where
    show (Var v) = "var " ++ show v
    show (Fn f ts) = "fApp " ++ show f ++ " " ++ show ts

instance Atom FOL String TermType where
    foldAtom f (R p ts) = f p ts
    zipAtoms f (R p1 ts1) (R p2 ts2) = f p1 ts1 p2 ts2
    apply' = R

instance FirstOrderFormula (Formula FOL) FOL String where
    -- type C.Term (Formula FOL) = Term
    -- type V (Formula FOL) = String
    -- type Pr (Formula FOL) = String
    -- type Fn (Formula FOL) = String -- ^ Atomic function type

    -- quant C.Exists v fm = H.Exists v fm
    -- quant C.Forall v fm = H.Forall v fm
    atomic = Atom
    foldFirstOrder q c p fm =
        case fm of
          F -> c FALSE
          T -> c TRUE
          Atom atom -> p atom
          Not fm' -> c ((:~:) fm')
          And fm1 fm2 -> c (BinOp fm1 (:&:) fm2)
          Or fm1 fm2 -> c (BinOp fm1 (:|:) fm2)
          Imp fm1 fm2 -> c (BinOp fm1 (:=>:) fm2)
          Iff fm1 fm2 -> c (BinOp fm1 (:<=>:) fm2)
          H.Forall v fm' -> q C.Forall v fm'
          H.Exists v fm' -> q C.Exists v fm'
    zipFirstOrder qu co pr fm1 fm2 =
        foldFirstOrder qu' co' pr' fm1
        where
          qu' op v p = foldFirstOrder (\ op2 v2 p2 -> qu op v p op2 v2 p2) (\ _ -> Nothing) (\ _ -> Nothing) fm2
          co' c = foldFirstOrder (\ _ _ _ -> Nothing) (\ c2 -> co c c2) (\ _ -> Nothing) fm2
          pr' atom = foldFirstOrder (\ _ _ _ -> Nothing) (\ _ -> Nothing) (pr atom) fm2

instance Arity String where
    arity _ = Nothing

instance Term TermType String String where
    -- type V Term = String
    -- type Fn Term = String
    vt = Var
    fApp = Fn
    foldTerm vfn _ (Var x) = vfn x
    foldTerm _ ffn (Fn f ts) = ffn f ts
    zipTerms = undefined
    skolemConstant v = "c_" ++ v
    skolemFunction v = "f_" ++ v

instance Variable String where
    variant x vars = if Set.member x vars then variant (x ++ "'") vars else x
    prefix p x = p ++ x
    prettyVariable = text

instance Function String where
    variantF x fns = if Set.member x fns then variantF (x ++ "'") fns else x

instance Show (Formula FOL) where
    show = showFirstOrder
