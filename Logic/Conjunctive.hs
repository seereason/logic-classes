{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, UndecidableInstances #-}
module Logic.Conjunctive
    ( Conjunctive(..)
    , NormalLogic(..)
    ) where

import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic

class (Ord v, Ord p, Ord f) => NormalLogic formula term v p f where
    nlNot :: formula -> formula
    nlPred :: p -> [term] -> formula
    nlEqual :: term -> term -> formula
    nlFold :: (formula -> r)
           -> (p -> [term] -> r)
           -> (term -> term -> r)
           -> formula
           -> r

-- |Any instance of FirstOrderLogic is also an instance of NormalLogic.
instance (FirstOrderLogic formula term v p f, Ord p, Ord f) => NormalLogic formula term v p f where
    nlNot = (.~.)
    nlPred = pApp
    nlEqual = (.=.)
    nlFold n p e = foldF n q b i p
        where
          q _ _ _ = error "nlFold: quantifier"
          b _ _ _ = error "nlFold: binOp"
          i t1 (:=:) t2 = e t1 t2
          i _ _ _ = error "nlFold: inquality"

-- |A class to represent formulas in Conjunctive Normal Form, which is 
-- the conjunction of a set of terms each which may or may not be negated.
class (FirstOrderLogic formula term v p f, Ord v, Ord p, Ord f) => Conjunctive cnf formula term v p f | cnf -> formula, cnf -> term where
    clauses :: cnf -> S.Set formula
    toConjunctive :: formula -> cnf
    fromConjunctive :: cnf -> formula
    fromConjunctive cnf =
        conj (S.elems (clauses cnf))
        where
          conj [] = pApp (fromBool True) []
          conj [x] = x
          conj (x:xs) = (x) .&. (conj xs)
