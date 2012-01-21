{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Logic.Classes.Formula
    ( Formula(foldAtoms, mapAtoms)
    ) where

class Formula formula atom where
    foldAtoms :: Formula formula atom => (r -> atom -> r) -> r -> formula -> r
    mapAtoms :: Formula formula atom => (atom -> formula) -> formula -> formula
