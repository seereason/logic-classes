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
import Data.Logic.Classes.Apply (Predicate)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), prettyFirstOrder)
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Pretty (Pretty(pretty))
import Data.Logic.Classes.Term (Term(..), Function)
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Normal.Implicative (implicativeNormalForm, ImplicativeForm, runNormal)
import qualified Data.Logic.Types.FirstOrder as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)

-- |Convert between the public and internal representations.
class Bijection p i where
    public :: i -> p
    intern :: p -> i

-- |The new Formula type is just a wrapper around the Native instance
-- (which eventually should be renamed the Internal instance.)  No
-- derived Eq or Ord instances.
data Formula v p f = Formula {unFormula :: N.Formula v p f} deriving (Data, Typeable, Show)

instance Bijection (Formula v p f) (N.Formula v p f) where
    public = Formula
    intern = unFormula

instance Bijection (Combination (Formula v p f)) (Combination (N.Formula v p f)) where
    public (BinOp x op y) = BinOp (public x) op (public y)
    public ((:~:) x) = (:~:) (public x)
    intern (BinOp x op y) = BinOp (intern x) op (intern y)
    intern ((:~:) x) = (:~:) (intern x)

instance Negatable (Formula v p f) where
    negatePrivate = Formula . negatePrivate . unFormula
    foldNegation normal inverted = foldNegation (normal . Formula) (inverted . Formula) . unFormula

instance (Constants (N.Formula v p f), Predicate p, Variable v, Function f) => Constants (Formula v p f) where
    fromBool = Formula . fromBool

instance (Constants (Formula v p f),
          Constants (N.Formula v p f),
          Variable v, Predicate p, Function f) => Combinable (Formula v p f) where
    x .<=>. y = Formula $ (unFormula x) .<=>. (unFormula y)
    x .=>.  y = Formula $ (unFormula x) .=>. (unFormula y)
    x .|.   y = Formula $ (unFormula x) .|. (unFormula y)
    x .&.   y = Formula $ (unFormula x) .&. (unFormula y)

{-
instance (Constants (N.Formula v p f),
          Show (N.Formula v p f),
          Predicate p, Variable v, Function f,
          Show p, Show v, Show f) => Show (Formula v p f) where
    showsPrec n x = showsPrec n (unFormula x)
-}

instance (Constants (Formula v p f), Constants (N.Formula v p f),
          Combinable (Formula v p f), Term (N.PTerm v f) v f,
          Predicate p) => FirstOrderFormula (Formula v p f) (N.Predicate p (N.PTerm v f)) v where
    for_all v x = public $ for_all v (intern x :: N.Formula v p f)
    exists v x = public $ exists v (intern x :: N.Formula v p f)
    foldFirstOrder qu co tf at f = foldFirstOrder qu' co' tf at (intern f :: N.Formula v p f)
        where qu' quant v form = qu quant v (public form)
              co' x = co (public x)
{-
    zipFirstOrder q c p f1 f2 = zipFirstOrder q' c' p (intern f1 :: N.Formula v p f) (intern f2 :: N.Formula v p f)
        where q' q1 v1 f1' q2 v2 f2' = q q1 v1 (public f1') q2 v2 (public f2')
              c' combine1 combine2 = c (public combine1) (public combine2)
-}
    atomic = Formula . atomic

-- |Here are the magic Ord and Eq instances
instance (Constants (N.Predicate p (N.PTerm v f)),
          Constants (Formula v p f),
          Constants (N.Formula v p f),
          Ord (N.Formula v p f),
          Predicate p, Function f, Variable v) => Ord (Formula v p f) where
    compare a b =
        let (a' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (intern a :: N.Formula v p f))
            (b' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (intern b :: N.Formula v p f)) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (Predicate p, Function f, Variable v, Constants (N.Predicate p (N.PTerm v f)),
          FirstOrderFormula (Formula v p f) (N.Predicate p (N.PTerm v f)) v) => Eq (Formula v p f) where
    a == b = compare a b == EQ

instance (Pretty v, Show v, Variable v,
          Pretty p, Show p, Predicate p,
          Pretty f, Show f, Function f) => Pretty (Formula v p f) where
    pretty formula = prettyFirstOrder (\ _prec a -> pretty a) pretty 0 formula

$(deriveSafeCopy 1 'base ''Formula)

$(deriveNewData [''Formula])
