{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- | The Apply class represents a type of atom the only supports predicate application.
module Data.Logic.Classes.Apply
    ( Apply(..)
    , Predicate
    , apply
    , zipApplys
    , apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7
    , showApply
    , prettyApply
    , varApply
    , substApply
    , pApp, pApp0, pApp1, pApp2, pApp3, pApp4, pApp5, pApp6, pApp7
    ) where

import Data.Data (Data)
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Formula (Formula(atomic))
import Data.Logic.Classes.Pretty (Pretty)
import Data.Logic.Classes.Term (Term, showTerm, prettyTerm, fvt, tsubst)
import Data.List (intercalate, intersperse)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, (<>), text, empty, parens, cat)

class (Arity p, Constants p, Eq p, Ord p, Data p, Pretty p) => Predicate p

class Predicate p => Apply atom p term | atom -> p term where
    foldApply :: (p -> [term] -> r) -> (Bool -> r) -> atom -> r
    apply' :: p -> [term] -> atom

-- | apply' with an arity check - clients should always call this.
apply :: Apply atom p term => p -> [term] -> atom
apply p ts =
    case arity p of
      Just n | n /= length ts -> error "arity"
      _ -> apply' p ts

zipApplys :: Apply atom p term =>
            (p -> [term] -> p -> [term] -> Maybe r)
         -> (Bool -> Bool -> Maybe r)
         -> atom -> atom -> Maybe r
zipApplys ap tf a1 a2 =
    foldApply ap' tf' a1
    where
      ap' p1 ts1 = foldApply (ap p1 ts1) (\ _ -> Nothing) a2
      tf' x1 = foldApply (\ _ _ -> Nothing) (tf x1) a2

apply0 p = if fromMaybe 0 (arity p) == 0 then apply' p [] else error "arity"
apply1 p a = if fromMaybe 1 (arity p) == 1 then apply' p [a] else error "arity"
apply2 p a b = if fromMaybe 2 (arity p) == 2 then apply' p [a,b] else error "arity"
apply3 p a b c = if fromMaybe 3 (arity p) == 3 then apply' p [a,b,c] else error "arity"
apply4 p a b c d = if fromMaybe 4 (arity p) == 4 then apply' p [a,b,c,d] else error "arity"
apply5 p a b c d e = if fromMaybe 5 (arity p) == 5 then apply' p [a,b,c,d,e] else error "arity"
apply6 p a b c d e f = if fromMaybe 6 (arity p) == 6 then apply' p [a,b,c,d,e,f] else error "arity"
apply7 p a b c d e f g = if fromMaybe 7 (arity p) == 7 then apply' p [a,b,c,d,e,f,g] else error "arity"

showApply :: (Apply atom p term, Term term v f, Show v, Show p, Show f) => atom -> String
showApply =
    foldApply (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))")
              (\ x -> if x then "true" else "false")

prettyApply :: (Apply atom p term, Term term v f) => (v -> Doc) -> (p -> Doc) -> (f -> Doc) -> Int -> atom -> Doc
prettyApply pv pp pf _prec atom =
    foldApply (\ p ts ->
                   pp p <> case ts of
                             [] -> empty
                             _ -> parens (cat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
              (\ x -> text (if x then "true" else "false"))
              atom

-- | Return the variables that occur in an instance of Apply.
varApply :: (Apply atom p term, Term term v f) => atom -> Set.Set v
varApply = foldApply (\ _ args -> Set.unions (map fvt args)) (const Set.empty)

substApply :: (Apply atom p term, Constants atom, Term term v f) => Map.Map v term -> atom -> atom
substApply env = foldApply (\ p args -> apply p (map (tsubst env) args)) fromBool

{-
instance (Apply atom p term, Term term v f, Constants atom) => Formula atom term v where
    allVariables = varApply
    freeVariables = varApply
    substitute = substApply
-}

pApp :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> [term] -> formula
pApp p ts = atomic (apply p ts :: atom)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> formula
pApp0 p = atomic (apply0 p :: atom)
pApp1 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> formula
pApp1 p a = atomic (apply1 p a :: atom)
pApp2 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> formula
pApp2 p a b = atomic (apply2 p a b :: atom)
pApp3 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = atomic (apply3 p a b c :: atom)
pApp4 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = atomic (apply4 p a b c d :: atom)
pApp5 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = atomic (apply5 p a b c d e :: atom)
pApp6 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = atomic (apply6 p a b c d e f :: atom)
pApp7 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
pApp7 p a b c d e f g = atomic (apply7 p a b c d e f g :: atom)
