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
import Data.Logic.Classes.Arity (Arity)
import Data.Logic.Classes.Combine (Combinable(..), Combine(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Pred(..))
import qualified Data.Logic.Types.FirstOrder as N
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..), )
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Normal.Implicative (implicativeNormalForm, ImplicativeForm)
import Data.Logic.Normal.Skolem (runNormal)
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
data Formula v p f = Formula {unFormula :: N.Formula v p f} deriving (Data, Typeable)

instance Bijection (Formula v p f) (N.Formula v p f) where
    public = Formula
    intern = unFormula

instance Bijection (Combine (Formula v p f)) (Combine (N.Formula v p f)) where
    public (BinOp x op y) = BinOp (public x) op (public y)
    public ((:~:) x) = (:~:) (public x)
    intern (BinOp x op y) = BinOp (intern x) op (intern y)
    intern ((:~:) x) = (:~:) (intern x)

instance Negatable (Formula v p f) where
    negated = negated . unFormula
    (.~.) = Formula . (.~.) . unFormula

instance (Arity p, Constants p, Ord v, Ord p, Ord f) => Constants (Formula v p f) where
    fromBool = Formula . fromBool

instance (Constants (Formula v p f), Constants (N.Formula v p f),
          Variable v, Show v, Ord v, Data v,
          Arity p, Constants p, Show p, Ord p, Data p,
          Skolem f, Show f, Ord f, Data f) => Combinable (Formula v p f) where
    x .<=>. y = Formula $ (unFormula x) .<=>. (unFormula y)
    x .=>.  y = Formula $ (unFormula x) .=>. (unFormula y)
    x .|.   y = Formula $ (unFormula x) .|. (unFormula y)
    x .&.   y = Formula $ (unFormula x) .&. (unFormula y)

instance (Constants (N.Formula v p f),
          Arity p, Variable v, Skolem f, Constants p,
          Show p, Show v, Show f,
          Ord f, Ord v, Ord p,
          Data p, Data v, Data f) => Show (Formula v p f) where
    showsPrec n x = showsPrec n (unFormula x)

instance (Constants (Formula v p f), Constants (N.Formula v p f),
          Variable v, Show v, Ord v, Data v,
          Show p, Ord p, Data p, Constants p, Arity p,
          Skolem f, Show f, Ord f, Data f) => Pred p (N.PTerm v f) (Formula v p f) where
    pApp0 p = (public :: N.Formula v p f -> Formula v p f) $ pApp0 p
    pApp1 p t1 = (public :: N.Formula v p f -> Formula v p f) $ pApp1 p (t1)
    pApp2 p t1 t2 = (public :: N.Formula v p f -> Formula v p f) $ pApp2 p (t1) (t2)
    pApp3 p t1 t2 t3 = (public :: N.Formula v p f -> Formula v p f) $ pApp3 (p) (t1) (t2) (t3)
    pApp4 p t1 t2 t3 t4 = (public :: N.Formula v p f -> Formula v p f) $ pApp4 (p) (t1) (t2) (t3) (t4)
    pApp5 p t1 t2 t3 t4 t5 = (public :: N.Formula v p f -> Formula v p f) $ pApp5 (p) (t1) (t2) (t3) (t4) (t5)
    pApp6 p t1 t2 t3 t4 t5 t6 = (public :: N.Formula v p f -> Formula v p f) $ pApp6 (p) (t1) (t2) (t3) (t4) (t5) (t6)
    pApp7 p t1 t2 t3 t4 t5 t6 t7 = (public :: N.Formula v p f -> Formula v p f) $ pApp7 (p) (t1) (t2) (t3) (t4) (t5) (t6) (t7)
    t1 .=. t2 = (public :: N.Formula v p f -> Formula v p f) $ (t1) .=. (t2)

instance (Constants (Formula v p f), Constants (N.Formula v p f),
          Combinable (Formula v p f), Term (N.PTerm v f) v f,
          Show v,
          Arity p, Constants p, Ord p, Data p, Show p,
          Ord f, Show f) => FirstOrderFormula (Formula v p f) (N.PTerm v f) v p f where
    for_all v x = public $ for_all v (intern x :: N.Formula v p f)
    exists v x = public $ exists v (intern x :: N.Formula v p f)
    foldFirstOrder q c p f = foldFirstOrder q' c' p (intern f :: N.Formula v p f)
        where q' quant v form = q quant v (public form)
              c' x = c (public x)
    zipFirstOrder q c p f1 f2 = zipFirstOrder q' c' p (intern f1 :: N.Formula v p f) (intern f2 :: N.Formula v p f)
        where q' q1 v1 f1' q2 v2 f2' = q q1 v1 (public f1') q2 v2 (public f2')
              c' combine1 combine2 = c (public combine1) (public combine2)

-- |Here are the magic Ord and Eq instances
instance ({- FirstOrderFormula (Formula v p f) (N.PTerm v f) v p f,
          Literal (N.Formula v p f) (N.PTerm v f) v p f,
          FirstOrderFormula (N.Formula v p f) (N.PTerm v f) v p f, -}
          Constants (Formula v p f), Constants (N.Formula v p f),
          Data v, Data f, Data p,
          Ord v, Ord p, Ord f,
          Show v, Show p, Show f,
          Arity p, Constants p, Skolem f, Variable v,
          Ord (N.Formula v p f)) => Ord (Formula v p f) where
    compare a b =
        let (a' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (intern a :: N.Formula v p f))
            (b' :: Set (ImplicativeForm (N.Formula v p f))) = runNormal (implicativeNormalForm (intern b :: N.Formula v p f)) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (FirstOrderFormula (Formula v p f) (N.PTerm v f) v p f) => Eq (Formula v p f) where
    a == b = compare a b == EQ

$(deriveSafeCopy 1 'base ''Formula)

$(deriveNewData [''Formula])
