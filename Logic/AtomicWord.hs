{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
module Logic.AtomicWord
    ( AtomicWord(..)
    ) where

import Data.Data (Data)
import Data.Monoid (Monoid(..))
import Data.String (IsString)
import qualified Data.Text as T
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
                            
-- | TPTP constant symbol\/predicate symbol\/function symbol
-- identifiers (they are output in single quotes unless they are
-- /lower_word/s).
newtype AtomicWord = AtomicWord T.Text
    deriving (Eq,Ord,Data,Typeable,Read,Show,Monoid,IsString)

instance Version AtomicWord
$(deriveSerialize ''AtomicWord)
$(deriveNewData [''AtomicWord])
