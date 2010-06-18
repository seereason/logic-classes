{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
module Logic.AtomicFunction
    ( AtomicFunction(..)
    ) where

import Data.Data (Data)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |An AtomicFunction is a type of Term which is applied to zero or more Terms
-- to compute a new Term.
data AtomicFunction w
    = AtomF w
    | LessThan                      -- Result is a truth value
    | Ratio                         -- Ratio of two numbers
    | PercentOf
    deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Version (AtomicFunction w)
$(deriveSerialize ''AtomicFunction)
$(deriveNewData [''AtomicFunction])
