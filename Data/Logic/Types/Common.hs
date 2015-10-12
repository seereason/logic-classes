{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Data.Logic.Types.Common where

import Data.Logic.Classes.Variable (IsVariable(..))
import qualified Data.Set as Set
import Text.PrettyPrint (text)

instance IsVariable String where
    variant x vars = if Set.member x vars then variant (x ++ "'") vars else x
    prefix p x = p ++ x
    prettyVariable = text

{-
instance Variable String where
    variant v vs =
        if Set.member v vs then variant (next v) (Set.insert v vs) else v
        where
          next :: String -> String
          next s =
              case break (not . isDigit) (reverse s) of
                (_, "") -> "x"
                ("", nondigits) -> nondigits ++ "2"
                (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)
-}
