{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -Wwarn -fno-warn-orphans #-}
-- |An instance of FirstOrderFormula which implements Eq and Ord by comparing
-- after conversion to normal form.  This helps us notice that formula which
-- only differ in ways that preserve identity, e.g. swapped arguments to a
-- commutative operator.

module Data.Logic.Types.FirstOrderPublic
    ( PFormula
    , Bijection(..)
    , Public
    , markPublic
    , unmarkPublic
    ) where

import Data.Data (Data)
import qualified Data.Logic.Types.FirstOrder as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set)
import FOL (HasEquals, HasPredicate, IsFunction, IsPredicate, IsVariable, IsQuantified(..))
import Formulas (HasBoolean(..), IsFormula(..))
import Prop (Marked(Mark, unMark'))
import Skolem (simpcnf')

-- |The new Formula type is just a wrapper around the Native instance
-- (which eventually should be renamed the Internal instance.)  No
-- derived Eq or Ord instances.
type PFormula v p f = Marked Public (N.NFormula v p f)
data Public = Public

deriving instance Data Public

markPublic :: a -> Marked Public a
markPublic = Mark

unmarkPublic :: Marked Public a -> a
unmarkPublic = unMark'
-- data PFormula v p f = Formula {unFormula :: N.NFormula v p f} deriving (Data, Typeable, Show)

-- |Convert between the public and internal representations.
class Bijection p i where
    public :: i -> p
    intern :: p -> i

instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (PFormula v p f) (N.NFormula v p f) where
    public = Mark
    intern = unMark'

#if 0
instance (Data p, Ord p, Data v, Ord v, Data f, Ord f) => Bijection (Combination (PFormula v p f)) (Combination (N.NFormula v p f)) where
    public x op y = (public x) op (public y)
    intern x op y = (intern x) op (intern y)

instance (IsVariable v, IsPredicate p, HasBoolean p, IsFunction f,
          IsLiteral (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFormula (PFormula v p f)  (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    foldLiteral' ho ne tf at fm = foldLiteral' (ho . markPublic) (ne . markPublic) tf at (unFormula fm)

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
         ) => IsCombinable (PFormula v p f) where
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
         ) => IsFormula (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    atomic = Formula . atomic
    overatoms = overatomsQuantified
    onatoms = onatomsQuantified

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => IsQuantified (PFormula v p f) (N.NPredicate p (N.NTerm v f)) v where
    quant q v x = public $ quant q v (intern x :: N.NFormula v p f)
    foldQuantified qu co ne tf at (PFormula f) = foldQuantified qu' co' ne' tf at (intern f :: N.NFormula v p f)
        where qu' op v form = qu op v (public form)
              ne' x = ne (public x)
              co' x = co (public x)

instance (IsVariable v, Data v, IsPredicate p, HasBoolean p, Data p, IsFunction f, Data f, HasEquals p, HasFunctions (N.NPredicate p (N.NTerm v f)) f
         ) => HasFunctions (PFormula v p f) f where
    funcs = foldQuantified (\_ _ fm -> funcs fm) co ne (\_ -> mempty) funcs
        where
          ne fm = funcs fm
          co lhs _ rhs = union (funcs lhs) (funcs rhs)

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => IsPropositional (PFormula v p f) (N.NPredicate p (N.NTerm v f)) where
    foldPropositional' ho co ne tf at f = foldPropositional' (ho . public) co' ne' tf at (intern f :: N.NFormula v p f)
        where co' x = co (public x)
              ne' x = ne (public x)

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          HasFixity (N.NPredicate p (N.NTerm v f)),
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
          {-HasPredicate (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f), HasEquate p, IsFunction f, IsVariable v-}
         ) => HasFixity (PFormula v p f) where
    fixity = fixityQuantified

instance (IsFirstOrder (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f,
          IsLiteral (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          HasFixity (N.NPredicate p (N.NTerm v f)),
          HasBoolean (N.NPredicate p (N.NTerm v f)),
          Data v, Data p, Data f
         ) => Pretty (PFormula v p f) where
    pPrint = prettyQuantified

instance (IsVariable v, IsPredicate p, HasBoolean p, IsFunction f,
          Data v, Data p, Data f, HasEquals p,
          HasFunctions (N.NPredicate p (N.NTerm v f)) f
         ) => IsFirstOrder (PFormula v p f) (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f) v f
#endif

-- | Here are the magic Ord and Eq instances - formulas will be Eq if
-- their normal forms are Eq up to renaming.
instance (IsVariable v, Data v, IsPredicate p, HasBoolean p, Data p, IsFunction f, Data f, HasEquals p
         ) => Ord (PFormula v p f) where
    compare a b =
        let (a' :: Set (Set (N.NFormula v p f))) = simpcnf' (unmarkPublic a)
            (b' :: Set (Set (N.NFormula v p f))) = simpcnf' (unmarkPublic b) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (HasPredicate (N.NPredicate p (N.NTerm v f)) p (N.NTerm v f), IsFormula (PFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFormula (N.NFormula v p f) (N.NPredicate p (N.NTerm v f)),
          IsFunction f, IsVariable v, HasBoolean (N.NPredicate p (N.NTerm v f)),
          IsQuantified (PFormula v p f) (N.NPredicate p (N.NTerm v f)) v,
          Data v, Data p, HasBoolean p, HasEquals p, Data f
         ) => Eq (PFormula v p f) where
    a == b = compare a b == EQ

$(deriveSafeCopy 1 'base ''Marked)
$(deriveSafeCopy 1 'base ''Public)
