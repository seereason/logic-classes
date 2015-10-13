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
import Data.Logic.Classes.Apply (IsPredicate, HasPredicate)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..))
import Data.Logic.Classes.Constants (HasBoolean(..))
import Data.Logic.Classes.Equals (HasEquals)
import Data.Logic.Classes.FirstOrder (IsQuantified(..), prettyFirstOrder, overatomsFirstOrder, onatomsFirstOrder, fixityFirstOrder)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(fixity))
import Data.Logic.Classes.Propositional (IsPropositional(..))
import Data.Logic.Classes.Term (Function)
import Data.Logic.Classes.Variable (IsVariable)
import Data.Logic.Normal.Implicative (implicativeNormalForm, ImplicativeForm, runNormal)
import qualified Data.Logic.Types.FirstOrder as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set)
import Data.Typeable (Typeable)

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

instance (Data p, Ord p, HasEquals p, Data v, Ord v, Data f, Ord f, Function f v) => IsNegatable (Formula v p f) where
    naiveNegate = Formula . naiveNegate . unFormula
    foldNegation normal inverted = foldNegation (normal . Formula) (inverted . Formula) . unFormula

instance (HasBoolean (N.Formula v p f), IsPredicate p, IsVariable v, Function f v) => HasBoolean (Formula v p f) where
    fromBool = Formula . fromBool
    asBool = asBool . unFormula

instance (C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          HasEquals p,
          HasBoolean (Formula v p f),
          HasBoolean (N.Formula v p f),
          IsVariable v, IsPredicate p, Function f v) => IsCombinable (Formula v p f) where
    x .<=>. y = Formula $ (unFormula x) .<=>. (unFormula y)
    x .=>.  y = Formula $ (unFormula x) .=>. (unFormula y)
    x .|.   y = Formula $ (unFormula x) .|. (unFormula y)
    x .&.   y = Formula $ (unFormula x) .&. (unFormula y)

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), HasEquals p, Function f v) => C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)) where
    atomic = Formula . C.atomic
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder
    prettyFormula = error "FIXME"

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)),
          C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          IsVariable v, HasEquals p, Function f v) => IsQuantified (Formula v p f) (N.Predicate p (N.PTerm v f)) v where
    quant q v x = public $ quant q v (intern x :: N.Formula v p f)
    foldQuantified qu co tf at f = foldQuantified qu' co' tf at (intern f :: N.Formula v p f)
        where qu' quant v form = qu quant v (public form)
              co' x = co (public x)

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)),
          C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          HasFixity (Formula v p f), IsVariable v, HasEquals p,
          -- Show v, Show p, Show f, 
          Function f v) => IsPropositional (Formula v p f) (N.Predicate p (N.PTerm v f)) where
    foldPropositional co tf at f = foldPropositional co' tf at (intern f :: N.Formula v p f)
        where co' x = co (public x)

-- |Here are the magic Ord and Eq instances
instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)),
          C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          HasEquals p, Function f v, IsVariable v) => Ord (Formula v p f) where
    compare a b =
        let (a' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (unFormula a))
            (b' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (unFormula b)) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)),
          C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          HasEquals p, Function f v, IsVariable v, HasBoolean (N.Predicate p (N.PTerm v f)),
          IsQuantified (Formula v p f) (N.Predicate p (N.PTerm v f)) v) => Eq (Formula v p f) where
    a == b = compare a b == EQ

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), HasEquals p, Function f v) => HasFixity (Formula v p f) where
    fixity = fixityFirstOrder

instance (HasPredicate (N.Predicate p (N.PTerm v f)) p (N.PTerm v f), C.IsFormula (Formula v p f) (N.Predicate p (N.PTerm v f)),
          C.IsFormula (N.Formula v p f) (N.Predicate p (N.PTerm v f)),
          IsVariable v, HasEquals p,
          Pretty v, Pretty p, Pretty f,
          -- Show v, Show p, Show f,
          Function f v) => Pretty (Formula v p f) where
    pPrint formula = prettyFirstOrder (\ _prec a -> pPrint a) pPrint 0 formula

$(deriveSafeCopy 1 'base ''Formula)
