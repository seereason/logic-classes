{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ScopedTypeVariables, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -Wwarn #-}
module Data.Logic.Types.Harrison.Prop
#if 1
    ( module Prop
    ) where

import Prop
#else
    ( Prop(..)
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Pretty
import Data.Logic.Classes.Propositional (showPropositional)
import Data.Logic.Types.Harrison.Formulas.Propositional (Formula(..))
import Prelude hiding (negate)
--import Text.PrettyPrint (text)

-- =========================================================================
-- Basic stuff for propositional logic: datatype, parsing and printing.
-- =========================================================================

newtype Prop = P {pname :: String} deriving (Read, Data, Typeable, Eq, Ord)

instance Show Prop where
    show x = "P " ++ show (pname x)

instance Pretty Prop where
    pPrint = text . pname

instance HasFixity Prop where
    fixity = const leafFixity

instance Show (Formula Prop) where
    show = showPropositional show

instance Show (Formula String) where
    show = showPropositional show
#endif
