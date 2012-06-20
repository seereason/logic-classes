{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
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
    , fromAtomEq
    , showAtomEq
    , prettyAtomEq
    , varAtomEq
    , substAtomEq
    , funcsAtomEq
    ) where

import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Apply (Predicate)
import Data.Logic.Classes.Arity (Arity(..))
import Data.Logic.Classes.Combine (Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool), ifElse)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Formula (Formula(atomic))
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Pretty (Pretty(pretty))
import Data.Logic.Classes.Term (Term, convertTerm, showTerm, prettyTerm, fvt, tsubst, funcs)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

-- | Its not safe to make Atom a superclass of AtomEq, because the Atom methods will fail on AtomEq instances.
class Predicate p => AtomEq atom p term | atom -> p term, term -> atom p where
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
data PredicateName p = Named p Int | Equals deriving (Eq, Ord, Show)

instance (Pretty p, Ord p) => Pretty (PredicateName p) where
    pretty Equals = text "="
    pretty (Named p _) = pretty p

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

arityError :: (Arity p) => p -> [a] -> t
arityError _p _ts = error "arity error"
-- arityError :: (Arity p, Pretty p) => p -> [a] -> t
-- arityError p ts = error $ "arity error: " ++ show (length ts) ++ " arguments applied to arity " ++ show (arity p) ++ " predicate " ++ show (pretty p)

pApp :: (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> [term] -> formula
pApp p ts = atomic (applyEq p ts)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: forall formula atom term v p. (FirstOrderFormula formula atom v, AtomEq atom p term) => p -> formula
pApp0 p = atomic (apply0 p :: atom)
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

{-
instance (AtomEq atom p term, Constants atom, Variable v, Term term v f) => Formula atom term v where
    substitute env = foldAtomEq (\ p args -> applyEq p (map (tsubst env) args)) fromBool (\ t1 t2 -> equals (tsubst env t1) (tsubst env t2))
    allVariables = foldAtomEq (\ _ args -> Set.unions (map fvt args)) (const Set.empty) (\ t1 t2 -> Set.union (fvt t1) (fvt t2))
    freeVariables = allVariables
-}

fromAtomEq :: (AtomEq atom1 p1 term1, Term term1 v1 f1,
               AtomEq atom2 p2 term2, Term term2 v2 f2, Constants atom2) =>
              (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> atom1 -> atom2
fromAtomEq cv cp cf atom =
    foldAtomEq (\ pr ts -> applyEq (cp pr) (map ct ts))
               fromBool
               (\ a b -> ct a `equals` ct b)
               atom
    where
      ct = convertTerm cv cf

showAtomEq :: forall atom term v p f. (AtomEq atom p term, Term term v f, Show v, Show p, Show f) => atom -> String
showAtomEq =
    foldAtomEq (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))")
               (\ x -> if x then "true" else "false")
               (\ t1 t2 -> "(" ++ parenTerm t1 ++ " .=. " ++ parenTerm t2 ++ ")")
    where
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"

prettyAtomEq :: (AtomEq atom p term, Term term v f) => (v -> Doc) -> (p -> Doc) -> (f -> Doc) -> Int -> atom -> Doc
prettyAtomEq pv pp pf prec atom =
    foldAtomEq (\ p ts -> pp p <> case ts of
                                    [] -> empty
                                    _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
               (text . ifElse "true" "false")
               (\ t1 t2 -> parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2))
               atom
    where
      parensIf False = id
      parensIf _ = parens . nest 1

-- | Return the variables that occur in an instance of AtomEq.
varAtomEq :: forall atom term v p f. (AtomEq atom p term, Term term v f) => atom -> Set.Set v
varAtomEq = foldAtomEq (\ _ args -> Set.unions (map fvt args)) (const Set.empty) (\ t1 t2 -> Set.union (fvt t1) (fvt t2))

substAtomEq :: (AtomEq atom p term, Constants atom, Term term v f) =>
               Map.Map v term -> atom -> atom
substAtomEq env = foldAtomEq (\ p args -> applyEq p (map (tsubst env) args)) fromBool (\ t1 t2 -> equals (tsubst env t1) (tsubst env t2))

funcsAtomEq :: (AtomEq atom p term, Term term v f, Ord f) => atom -> Set.Set (f, Int)
funcsAtomEq = foldAtomEq (\ _ ts -> Set.unions (map funcs ts)) (const Set.empty) (\ t1 t2 -> Set.union (funcs t1) (funcs t2))
