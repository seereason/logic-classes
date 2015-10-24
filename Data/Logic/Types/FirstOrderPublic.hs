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
