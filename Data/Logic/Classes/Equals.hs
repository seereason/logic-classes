{-# LANGUAGE FlexibleContexts, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
-- | Support for equality.
module Data.Logic.Classes.Equals
    ( PredicateEq(..)
    , AtomEq(..)
    , showFirstOrderFormulaEq
    , (.=.), (≡)
    , (.!=.), (≢)
    ) where

import Data.Logic.Classes.Arity
import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Propositional (showPropositionalFormula)
import Data.Logic.Classes.Term (Term(..))

class PredicateEq p where
    eqp :: p

class (Atom atom p term, PredicateEq p) => AtomEq atom p term | atom -> p term where
    foldAtomEq :: (p -> [term] -> r) -> (term -> term -> r) -> atom -> r
    zipAtomsEq :: (p -> [term] -> p -> [term] -> r) -> (term -> term -> term -> term -> r) -> atom -> atom -> Maybe r
    equals :: term -> term -> atom    

showFirstOrderFormulaEq :: (FirstOrderFormula fof atom v, AtomEq atom p term, Show term, Show v, Show p) => fof -> String
showFirstOrderFormulaEq fm =
    fst (sfo fm)
    where
      sfo fm = foldFirstOrder q c pr fm
      q op v f = (showQuant op ++ " " ++ show v ++ " " ++ parens quantPrec (sfo f), quantPrec)
      -- This code is duplicated from Propositional, but the recursive
      -- calls are to showFirstOrderFormula
      c FALSE = ("false", 0)
      c TRUE = ("true", 0)
      c ((:~:) p) =
          let prec' = 5 in
          ("(.~.)" ++ parens prec' (sfo p), prec')
      c (BinOp p op q) = (parens (opPrec op) (sfo p) ++ " " ++ showBinOp op ++ " " ++ parens (opPrec op) (sfo q), opPrec op)
      pr = foldAtomEq (\ p ts -> ("pApp " ++ show p ++ " " ++ show ts, 6))
                      (\ t1 t2 -> ("(" ++ show t1 ++ ") .=. (" ++ show t2 ++ ")", 6))
      showBinOp (:<=>:) = ".<=>."
      showBinOp (:=>:) = ".=>."
      showBinOp (:&:) = ".&."
      showBinOp (:|:) = ".|."
      showQuant Exists = "exists"
      showQuant Forall = "for_all"
      opPrec (:|:) = 3
      opPrec (:&:) = 4
      opPrec (:=>:) = 2
      opPrec (:<=>:) = 2
      quantPrec = 1
      parens :: Int -> (String, Int) -> String
      parens prec' (s, prec) = if prec >= prec' then "(" ++ s ++ ")" else s

(.=.) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
a .=. b = atomic (equals a b)

(.!=.) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
a .!=. b = (.~.) (a .=. b)

(≡) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
(≡) = (.=.)

(≢) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
(≢) = (.!=.)
