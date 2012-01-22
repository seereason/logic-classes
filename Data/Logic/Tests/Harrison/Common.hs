{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}
module Data.Logic.Tests.Harrison.Common where

import Data.Logic.Types.Harrison.Equal (FOLEQ(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))

deriving instance Show FOLEQ
deriving instance Show (Formula FOLEQ)

    