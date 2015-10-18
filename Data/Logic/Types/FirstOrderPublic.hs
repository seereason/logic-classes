{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -Wwarn -fno-warn-orphans #-}
-- |An instance of FirstOrderFormula which implements Eq and Ord by comparing
-- after conversion to normal form.  This helps us notice that formula which
-- only differ in ways that preserve identity, e.g. swapped arguments to a
-- commutative operator.

module Data.Logic.Types.FirstOrderPublic
    ( Formula(..)
    , Bijection(..)
    ) where

import Data.Data (Data)
import Data.Function (on)
import qualified Data.Logic.Instances.Test as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set)
import Data.Typeable (Typeable)
import FOL (FOL, HasPredicate, HasEquals, IsFirstOrder, IsFunction, IsPredicate, IsVariable, IsQuantified(..),
            overatomsFirstOrder, onatomsFirstOrder, fixityFirstOrder)
import Formulas (HasBoolean(..))
import Formulas (IsCombinable(..), Combination(..))
import Formulas (IsNegatable(..))
import Formulas (prettyFormula)
import qualified Formulas as C
import Lit (IsLiteral)
import Pretty (Pretty(pPrint), HasFixity(fixity))
import Pretty (rootFixity, Side(Unary))
import Prop (IsPropositional(..))
import Skolem (simpcnf')

-- |Convert between the public and internal representations.
class Bijection p i where
    public :: i -> p
    intern :: p -> i

-- |The new Formula type is just a wrapper around the Native instance
-- (which eventually should be renamed the Internal instance.)  No
-- derived Eq or Ord instances.
data Formula v p f = Formula {unFormula :: N.Formula v p f} deriving (Data, Typeable, Show)

instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (Formula v p f) (N.Formula v p f) where
    public = Formula
    intern = unFormula

instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (Combination (Formula v p f)) (Combination (N.Formula v p f)) where
    public (BinOp x op y) = BinOp (public x) op (public y)
    public ((:~:) x) = (:~:) (public x)
    intern (BinOp x op y) = BinOp (intern x) op (intern y)
    intern ((:~:) x) = (:~:) (intern x)

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          HasEquals p {-, IsFunction f, IsVariable v, Data p, Ord p, Data v, Ord v, Data f, Ord f-}) => IsNegatable (Formula v p f) where
    naiveNegate = Formula . naiveNegate . unFormula
    foldNegation' inverted normal = foldNegation' (inverted . Formula) (normal . Formula) . unFormula

instance (HasBoolean (N.Formula v p f), IsPredicate p, IsVariable v, IsFunction f) => HasBoolean (Formula v p f) where
    fromBool = Formula . fromBool
    asBool = asBool . unFormula

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f))
{-
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          HasEquals p,
          HasBoolean (Formula v p f),
          HasBoolean (N.Formula v p f),
          ,
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          IsVariable v, IsPredicate p (N.Term v f), IsFunction f-}) => IsCombinable (Formula v p f) where
    foldCombination dj cj imp iff other (Formula fm) =
        foldCombination (dj `on` Formula) (cj `on` Formula) (imp `on` Formula) (iff `on` Formula) (other . Formula) fm
    x .<=>. y = Formula $ (unFormula x) .<=>. (unFormula y)
    x .=>.  y = Formula $ (unFormula x) .=>. (unFormula y)
    x .|.   y = Formula $ (unFormula x) .|. (unFormula y)
    x .&.   y = Formula $ (unFormula x) .&. (unFormula y)

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          HasEquals p, Data v, Data p, Data f
         {-, HasPredicate (FOL p (N.Term v f)) p (N.Term v f), IsFunction f, IsVariable v-}) => C.IsFormula (Formula v p f) (FOL p (N.Term v f)) where
    atomic = Formula . C.atomic
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder
    prettyFormula = error "FIXME"

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          HasEquals p, Data v, Data p, Data f
          {- HasPredicate (FOL p (N.Term v f)) p (N.Term v f), C.IsFormula (Formula v p f) (FOL p (N.Term v f)),
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          IsVariable v, HasEquals p, IsFunction f -}) => IsQuantified (Formula v p f) (FOL p (N.Term v f)) v where
    quant q v x = public $ quant q v (intern x :: N.Formula v p f)
    foldQuantified qu co tf at f = foldQuantified qu' co' tf at (intern f :: N.Formula v p f)
        where qu' op v form = qu op v (public form)
              co' x = co (public x)

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          Data v, Data p, Data f
          {-HasPredicate (FOL p (N.Term v f)) p (N.Term v f), C.IsFormula (Formula v p f) (FOL p (N.Term v f)),
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          HasFixity (Formula v p f), IsVariable v, HasEquals p,
          -- Show v, Show p, Show f, 
          IsFunction f-}) => IsPropositional (Formula v p f) (FOL p (N.Term v f)) where
    foldPropositional co tf at f = foldPropositional co' tf at (intern f :: N.Formula v p f)
        where co' x = co (public x)

-- |Here are the magic Ord and Eq instances
instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          HasBoolean (FOL p (N.Term v f)),
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          Data v, Data p, Data f
          {-HasPredicate (FOL p (N.Term v f)) p (N.Term v f), C.IsFormula (Formula v p f) (FOL p (N.Term v f)),
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          HasEquals p, IsFunction f, IsVariable v -}) => Ord (Formula v p f) where
    compare a b =
        let (a' :: Set (Set (N.Formula v p f))) = simpcnf' (unFormula a)
            (b' :: Set (Set (N.Formula v p f))) = simpcnf' (unFormula b) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (HasPredicate (FOL p (N.Term v f)) p (N.Term v f), C.IsFormula (Formula v p f) (FOL p (N.Term v f)),
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          HasEquals p, IsFunction f, IsVariable v, HasBoolean (FOL p (N.Term v f)),
          IsQuantified (Formula v p f) (FOL p (N.Term v f)) v) => Eq (Formula v p f) where
    a == b = compare a b == EQ

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          HasFixity (FOL p (N.Term v f)),
          HasBoolean (FOL p (N.Term v f)),
          HasEquals p,
          Data v, Data p, Data f
          {-HasPredicate (FOL p (N.Term v f)) p (N.Term v f), HasEquals p, IsFunction f, IsVariable v-}) => HasFixity (Formula v p f) where
    fixity = fixityFirstOrder

instance (IsFirstOrder (N.Formula v p f) (FOL p (N.Term v f)) p (N.Term v f) v f,
          IsLiteral (Formula v p f) (FOL p (N.Term v f)),
          HasFixity (FOL p (N.Term v f)),
          HasBoolean (FOL p (N.Term v f)),
          Data v, Data p, Data f
          {-HasPredicate (FOL p (N.Term v f)) p (N.Term v f), C.IsFormula (Formula v p f) (FOL p (N.Term v f)),
          C.IsFormula (N.Formula v p f) (FOL p (N.Term v f)),
          IsVariable v, HasEquals p,
          Pretty v, Pretty p, Pretty f,
          -- Show v, Show p, Show f,
          IsFunction f-}) => Pretty (Formula v p f) where
    pPrint = prettyFormula rootFixity Unary

$(deriveSafeCopy 1 'base ''Formula)
