{-# LANGUAGE FlexibleContexts, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
-- | Support for equality.
module Data.Logic.Classes.Equals
    ( AtomEq(..)
    , applyEq
    , PredicateName(..)
    , zipAtomsEq
    , apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7
    , pApp, pApp0, pApp1, pApp2, pApp3, pApp4, pApp5, pApp6, pApp7
    , showFirstOrderFormulaEq
    , (.=.), (≡)
    , (.!=.), (≢)
    ) where

import Data.Logic.Classes.Arity (Arity(..))
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Negate ((.~.))
import Data.Maybe (fromMaybe)

-- | Its not safe to make Atom a superclass of AtomEq, because the Atom methods will fail on AtomEq instances.
class (Arity p, Constants p, Eq p, Show p) => AtomEq atom p term | atom -> p term, term -> atom p where
    foldAtomEq :: (p -> [term] -> r) -> (Bool -> r) -> (term -> term -> r) -> atom -> r
    equals :: term -> term -> atom
    applyEq' :: p -> [term] -> atom

-- | applyEq' with an arity check - clients should always call this.
applyEq :: AtomEq atom p term => p -> [term] -> atom
applyEq p ts =
    case arity p of
      Just n | n /= length ts -> arityError p ts
      _ -> applyEq' p ts

-- | A way to represent any predicate's name.  Frequently the equality
-- predicate has no standalone representation in the p type, it is
-- just a constructor in the atom type, or even the formula type.
data Ord p => PredicateName p = Named p Int | Equals deriving (Eq, Ord)

zipAtomsEq :: AtomEq atom p term =>
              (p -> [term] -> p -> [term] -> Maybe r)
           -> (Bool -> Bool -> Maybe r)
           -> (term -> term -> term -> term -> Maybe r)
           -> atom -> atom -> Maybe r
zipAtomsEq ap tf eq a1 a2 =
    foldAtomEq ap' tf' eq' a1
    where
      ap' p1 ts1 = foldAtomEq (ap p1 ts1) (\ _ -> Nothing) (\ _ _ -> Nothing) a2
      tf' x1 = foldAtomEq (\ _ _ -> Nothing) (tf x1) (\ _ _ -> Nothing) a2
      eq' t1 t2 = foldAtomEq (\ _ _ -> Nothing) (\ _ -> Nothing) (eq t1 t2) a2

apply0 :: AtomEq atom p term => p -> atom
apply0 p = if fromMaybe 0 (arity p) == 0 then applyEq' p [] else arityError p []
apply1 :: AtomEq atom p a => p -> a -> atom
apply1 p a = if fromMaybe 1 (arity p) == 1 then applyEq' p [a] else arityError p [a]
apply2 :: AtomEq atom p a => p -> a -> a -> atom
apply2 p a b = if fromMaybe 2 (arity p) == 2 then applyEq' p [a,b] else arityError p [a,b]
apply3 :: AtomEq atom p a => p -> a -> a -> a -> atom
apply3 p a b c = if fromMaybe 3 (arity p) == 3 then applyEq' p [a,b,c] else arityError p [a,b,c]
apply4 :: AtomEq atom p a => p -> a -> a -> a -> a -> atom
apply4 p a b c d = if fromMaybe 4 (arity p) == 4 then applyEq' p [a,b,c,d] else arityError p [a,b,c,d]
apply5 :: AtomEq atom p a => p -> a -> a -> a -> a -> a -> atom
apply5 p a b c d e = if fromMaybe 5 (arity p) == 5 then applyEq' p [a,b,c,d,e] else arityError p [a,b,c,d,e]
apply6 :: AtomEq atom p a => p -> a -> a -> a -> a -> a -> a -> atom
apply6 p a b c d e f = if fromMaybe 6 (arity p) == 6 then applyEq' p [a,b,c,d,e,f] else arityError p [a,b,c,d,e,f]
apply7 :: AtomEq atom p a => p -> a -> a -> a -> a -> a -> a -> a -> atom
apply7 p a b c d e f g = if fromMaybe 7 (arity p) == 7 then applyEq' p [a,b,c,d,e,f,g] else arityError p [a,b,c,d,e,f,g]

arityError :: (Arity p, Show p) => p -> [a] -> t
arityError p ts = error $ "arity error for " ++ show p ++ ": expected " ++ show (arity p) ++ ", got " ++ show (length ts)

pApp :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> [term] -> formula
pApp p ts = atomic (applyEq p ts)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> formula
pApp0 p = atomic (apply0 p)
pApp1 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> formula
pApp1 p a = atomic (apply1 p a)
pApp2 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> formula
pApp2 p a b = atomic (apply2 p a b)
pApp3 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = atomic (apply3 p a b c)
pApp4 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = atomic (apply4 p a b c d)
pApp5 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = atomic (apply5 p a b c d e)
pApp6 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = atomic (apply6 p a b c d e f)
pApp7 :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
pApp7 p a b c d e f g = atomic (apply7 p a b c d e f g)

showFirstOrderFormulaEq :: (FirstOrderFormula fof atom v, AtomEq atom p term, Show term, Show v, Show p) => fof -> String
showFirstOrderFormulaEq fm =
    fst (sfo fm)
    where
      sfo p = foldFirstOrder qu co tf pr p
      qu op v f = (showQuant op ++ " " ++ show v ++ " " ++ parens quantPrec (sfo f), quantPrec)
      co ((:~:) p) =
          let prec' = 5 in
          ("(.~.)" ++ parens prec' (sfo p), prec')
      co (BinOp p op q) = (parens (opPrec op) (sfo p) ++ " " ++ showBinOp op ++ " " ++ parens (opPrec op) (sfo q), opPrec op)
      tf x = (if x then "true" else "false", 0)
      pr = foldAtomEq (\ p ts -> ("pApp " ++ show p ++ " " ++ show ts, 6))
                      (\ x -> (if x then "true" else "false", 0))
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

infix 5 .=., .!=., ≡, ≢

(.=.) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
a .=. b = atomic (equals a b)

(.!=.) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
a .!=. b = (.~.) (a .=. b)

(≡) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
(≡) = (.=.)

(≢) :: (FirstOrderFormula fof atom v, AtomEq atom p term) => term -> term -> fof
(≢) = (.!=.)
