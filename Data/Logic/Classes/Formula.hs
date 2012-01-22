{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Logic.Classes.Formula
    ( Formula(atomic, foldAtoms, mapAtoms)
    ) where

class Formula formula atom where
    atomic :: atom -> formula
    foldAtoms :: Formula formula atom => (r -> atom -> r) -> r -> formula -> r
    mapAtoms :: Formula formula atom => (atom -> formula) -> formula -> formula
