{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Data.Logic.Classes.Formula
    ( IsFormula(atomic, overatoms, onatoms)
    ) where

class IsFormula formula atom | formula -> atom where
    atomic :: atom -> formula
    overatoms :: (atom -> r -> r) -> formula -> r -> r
    onatoms :: (atom -> formula) -> formula -> formula
