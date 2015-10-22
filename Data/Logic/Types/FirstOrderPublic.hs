{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -Wwarn -fno-warn-orphans #-}
-- |An instance of FirstOrderFormula which implements Eq and Ord by comparing
-- after conversion to normal form.  This helps us notice that formula which
-- only differ in ways that preserve identity, e.g. swapped arguments to a
-- commutative operator.

module Data.Logic.Types.FirstOrderPublic
    ( PFormula(..)
    , Bijection(..)
    ) where

import Data.Data (Data)
import Data.Function (on)
import qualified Data.Logic.Types.FirstOrder as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set, union)
import Data.Typeable (Typeable)
import FOL (fixityFirstOrder, HasEquals, HasFunctions(funcs), HasPredicate,
            IsFirstOrder, IsFunction, IsPredicate, IsVariable, IsQuantified(..),
            overatomsFirstOrder, onatomsFirstOrder, prettyQuantified)
import Formulas (HasBoolean(..), IsCombinable(..), Combination(..), IsFormula(..), IsNegatable(..))
import Lit (IsLiteral(..))
import Pretty (Pretty(pPrint), HasFixity(fixity))
import Prop (IsPropositional(..))
import Skolem (simpcnf')

-- |Convert between the public and internal representations.
class Bijection p i where
    public :: i -> p
    intern :: p -> i

-- |The new Formula type is just a wrapper around the Native instance
-- (which eventually should be renamed the Internal instance.)  No
-- derived Eq or Ord instances.
data PFormula v p f = Formula {unFormula :: N.NFormula v p f} deriving (Data, Typeable, Show)

instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (PFormula v p f) (N.NFormula v p f) where
    public = Formula
    intern = unFormula

instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (Combination (PFormula v p f)) (Combination (N.NFormula v p f)) where
    public (BinOp x op y) = BinOp (public x) op (public y)
    public ((:~:) x) = (:~:) (public x)
    intern (BinOp x op y) = BinOp (intern x) op (intern y)
    intern ((:~:) x) = (:~:) (intern x)

instance (IsVariable v, IsPredicate p, IsFunction f,
          IsLiteral (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFormula (PFormula v p f)  (N.NPredicate p (N.NTerm v f)),
          HasBoolean p, Data v, Data p, Data f
         ) => IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    foldLiteral ne tf at fm = foldLiteral (ne . Formula) tf at (unFormula fm)

-- instance (IsVariable v, IsPredicate p, IsFunction f, HasBoolean p) => IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f

instance (IsVariable v, IsPredicate p, IsFunction f, HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f))
          ) => IsNegatable (PFormula v p f) where
    naiveNegate = Formula . naiveNegate . unFormula
    foldNegation' inverted normal = foldNegation' (inverted . Formula) (normal . Formula) . unFormula

instance (HasBoolean (N.NFormula v p f), IsPredicate p, IsVariable v, IsFunction f) => HasBoolean (PFormula v p f) where
    fromBool = Formula . fromBool
    asBool = asBool . unFormula

instance (IsVariable v, IsPredicate p, IsFunction f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f))
{-
          IsFormula (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)),
          HasEquate p,
          HasBoolean (Formula v p f),
          HasBoolean (N.NFormula v p f),
          ,
          IsLiteral (Formula v p f) (N.NPredicate p (N.NTerm v f)),
          IsVariable v, IsPredicate p (N.NTerm v f), IsFunction f-}) => IsCombinable (PFormula v p f) where
    foldCombination dj cj imp iff other (Formula fm) =
        foldCombination (dj `on` Formula) (cj `on` Formula) (imp `on` Formula) (iff `on` Formula) (other . Formula) fm
    x .<=>. y = Formula $ (unFormula x) .<=>. (unFormula y)
    x .=>.  y = Formula $ (unFormula x) .=>. (unFormula y)
    x .|.   y = Formula $ (unFormula x) .|. (unFormula y)
    x .&.   y = Formula $ (unFormula x) .&. (unFormula y)

instance (IsVariable v, IsPredicate p, IsFunction f,
          IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         {-, HasPredicate (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f), IsFunction f, IsVariable v-}
         ) => IsFormula (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    atomic = Formula . atomic
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => IsQuantified (PFormula v p f) (N.NPredicate p (N.NTerm v f)) v where
    quant q v x = public $ quant q v (intern x :: N.NFormula v p f)
    foldQuantified qu co tf at f = foldQuantified qu' co' tf at (intern f :: N.NFormula v p f)
        where qu' op v form = qu op v (public form)
              co' x = co (public x)

instance (IsVariable v, Data v, IsPredicate p, Data p, IsFunction f, Data f, HasBoolean p, HasEquals p, HasFunctions (N.NPredicate p (N.NTerm v f)) f
         ) => HasFunctions (PFormula v p f) f where
    funcs = foldQuantified (\_ _ fm -> funcs fm) co (\_ -> mempty) funcs
        where
          co ((:~:) fm) = funcs fm
          co (BinOp lhs _ rhs) = union (funcs lhs) (funcs rhs)

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => IsPropositional (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    foldPropositional' ho co tf at f = foldPropositional' (ho . public) co' tf at (intern f :: N.NFormula v p f)
        where co' x = co (public x)

-- |Here are the magic Ord and Eq instances
instance (IsVariable v, Data v, IsPredicate p, Data p, IsFunction f, Data f, HasBoolean p, HasEquals p
         ) => Ord (PFormula v p f) where
    compare a b =
        let (a' :: Set (Set (N.NFormula v p f))) = simpcnf' (unFormula a)
            (b' :: Set (Set (N.NFormula v p f))) = simpcnf' (unFormula b) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (HasPredicate (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f), IsFormula (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFormula (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFunction f, IsVariable v, HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsQuantified (PFormula v p f) (N.NPredicate p (N.NTerm v f)) v
         ) => Eq (PFormula v p f) where
    a == b = compare a b == EQ

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          HasFixity (N.NPredicate p (N.NTerm v f)),
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
          {-HasPredicate (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f), HasEquate p, IsFunction f, IsVariable v-}
         ) => HasFixity (PFormula v p f) where
    fixity = fixityFirstOrder

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          HasFixity (N.NPredicate p (N.NTerm v f)),
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => Pretty (PFormula v p f) where
    pPrint = prettyQuantified

instance (IsVariable v, IsPredicate p, IsFunction f,
          Data v, Data p, Data f, HasBoolean p, HasEquals p,
          HasFunctions (N.NPredicate p (N.NTerm v f)) f) => IsFirstOrder (PFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f

$(deriveSafeCopy 1 'base ''PFormula)
