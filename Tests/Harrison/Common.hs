{-# LANGUAGE FlexibleInstances, StandaloneDeriving #-}
module Harrison.Common where

import Data.Logic.Types.Harrison.Equal (FOLEQ(..))
import Data.Logic.Types.Harrison.Formulas.FirstOrder (Formula(..))

deriving instance Show FOLEQ
deriving instance Show (Formula FOLEQ)

    
