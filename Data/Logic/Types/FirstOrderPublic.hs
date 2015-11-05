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
    -- , Bijection(..)
    , Marked(Mark, unMark')
    , Public
    , markPublic
    , unmarkPublic
    ) where

import Data.Data (Data)
import Data.Generics (Typeable)
import qualified Data.Logic.Types.FirstOrder as N
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Set (Set)
import Formulas (HasBoolean(..), IsCombinable(..), IsNegatable(..), IsAtom, IsFormula(..))
import FOL (IsFirstOrder, IsFunction, IsPredicate, IsQuantified(..), IsVariable)
import Lit (IsLiteral(..))
import Pretty (HasFixity(..), Pretty(..))
import Prop (IsPropositional(..))
import Skolem (simpcnf')

data Marked mark a = Mark {unMark' :: a} deriving (Data, Typeable, Read)

instance (IsQuantified formula, IsPropositional (Marked mk formula)) => IsQuantified (Marked mk formula) where
    type VarOf (Marked mk formula) = VarOf formula
    quant q v x = Mark $ quant q v (unMark' x)
    foldQuantified qu co ne tf at f = foldQuantified qu' co' ne' tf at (unMark' f)
        where qu' op v f' = qu op v (Mark f')
              ne' x = ne (Mark x)
              co' x op y = co (Mark x) op (Mark y)

instance IsFirstOrder formula => IsFirstOrder (Marked mk formula)

instance IsFormula formula => IsFormula (Marked mk formula) where
    type AtomOf (Marked mk formula) = AtomOf formula
    atomic = Mark . atomic
    overatoms at (Mark fm) = overatoms at fm
    onatoms at (Mark fm) = Mark (onatoms (unMark' . at) fm)

instance HasBoolean formula => HasBoolean (Marked mk formula) where
    asBool (Mark x) = asBool x
    fromBool x = Mark (fromBool x)

instance IsNegatable formula => IsNegatable (Marked mk formula) where
    naiveNegate (Mark x) = Mark (naiveNegate x)
    foldNegation ot ne (Mark x) = foldNegation (ot . Mark) (ne . Mark) x

instance IsCombinable formula => IsCombinable (Marked mk formula) where
    (Mark a) .|. (Mark b) = Mark (a .|. b)
    (Mark a) .&. (Mark b) = Mark (a .&. b)
    (Mark a) .=>. (Mark b) = Mark (a .=>. b)
    (Mark a) .<=>. (Mark b) = Mark (a .<=>. b)
    foldCombination other dj cj imp iff fm =
        foldCombination (\a -> other a)
                        (\a b -> dj a b)
                        (\a b -> cj a b)
                        (\a b -> imp a b)
                        (\a b -> iff a b)
                        fm

instance (IsLiteral formula, IsNegatable formula) => IsLiteral (Marked mk formula) where
    foldLiteral' ho ne tf at (Mark x) = foldLiteral' (ho . Mark) (ne . Mark) tf at x

instance HasFixity formula => HasFixity (Marked mk formula) where
    fixity (Mark x) = fixity x

instance Pretty formula => Pretty (Marked mk formula) where
    pPrint = pPrint . unMark'

instance IsPropositional formula => IsPropositional (Marked mk formula) where
    foldPropositional' ho co ne tf at (Mark x) = foldPropositional' (ho . Mark) co' (ne . Mark) tf at x
        where
          co' lhs op rhs = co (Mark lhs) op (Mark rhs)

-- |The new Formula type is just a wrapper around the Native instance
-- (which eventually should be renamed the Internal instance.)  No
-- derived Eq or Ord instances, we define them below.
type PFormula v p f = Marked Public (N.NFormula v p f)
data Public = Public

deriving instance Data Public

markPublic :: a -> Marked Public a
markPublic = Mark

unmarkPublic :: Marked Public a -> a
unmarkPublic = unMark'

instance Show formula => Show (Marked Public formula) where
    show (Mark fm) = "markPublic (" ++ show fm ++ ")"

-- | Here are the magic Ord and Eq instances - formulas will be Eq if
-- their normal forms are Eq up to renaming.
instance (IsAtom (N.NPredicate p (N.NTerm v f)), IsVariable v, Data v, IsPredicate p, Data p, IsFunction f, Data f
         ) => Ord (PFormula v p f) where
    compare a b =
        let (a' :: Set (Set (N.NFormula v p f))) = simpcnf' (unmarkPublic a)
            (b' :: Set (Set (N.NFormula v p f))) = simpcnf' (unmarkPublic b) in
        case compare a' b' of
          EQ -> EQ
          x -> {- if isRenameOf a' b' then EQ else -} x

instance (IsAtom (N.NPredicate p (N.NTerm v f)), IsVariable v, Data v, IsPredicate p, Data p, IsFunction f, Data f
         ) => Eq (PFormula v p f) where
    a == b = compare a b == EQ

$(deriveSafeCopy 1 'base ''Marked)
$(deriveSafeCopy 1 'base ''Public)
