{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
-- | The Apply class represents a type of atom the only supports predicate application.
module Data.Logic.Classes.Apply
    ( HasPredicate(..)
    , IsPredicate
    , apply
    , zipApplys
    -- , apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7
    , showApply
    , prettyApply
    , varApply
    , substApply
    , pApp, pApp0, pApp1, pApp2, pApp3, pApp4, pApp5, pApp6, pApp7
    ) where

import Data.Data (Data)
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Formula (IsFormula(atomic))
import Data.Logic.Classes.Pretty (Pretty)
import Data.Logic.Classes.Term (IsTerm, showTerm, prettyTerm, fvt, tsubst)
import Data.List (intercalate, intersperse)
--import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, (<>), text, empty, parens, cat)

class (Arity p, HasBoolean p, Eq p, Ord p, Data p, Pretty p) => IsPredicate p

class IsPredicate p => HasPredicate atom p term | atom -> p term where
    foldPredicate :: (p -> [term] -> r) -> atom -> r
    applyPredicate :: p -> [term] -> atom

-- | applyPredicate with an arity check - clients should always call this.
apply :: HasPredicate atom p term => p -> [term] -> atom
apply p ts =
    case arity p of
      Just n | n /= length ts -> error "arity"
      _ -> applyPredicate p ts

zipApplys :: HasPredicate atom p term =>
            (p -> [term] -> p -> [term] -> Maybe r)
         -> atom -> atom -> Maybe r
zipApplys ap a1 a2 =
    foldPredicate ap' a1
    where
      ap' p1 ts1 = foldPredicate (ap p1 ts1) a2

{-
apply0 p = if fromMaybe 0 (arity p) == 0 then applyPredicate p [] else error "arity"
apply1 p a = if fromMaybe 1 (arity p) == 1 then applyPredicate p [a] else error "arity"
apply2 p a b = if fromMaybe 2 (arity p) == 2 then applyPredicate p [a,b] else error "arity"
apply3 p a b c = if fromMaybe 3 (arity p) == 3 then applyPredicate p [a,b,c] else error "arity"
apply4 p a b c d = if fromMaybe 4 (arity p) == 4 then applyPredicate p [a,b,c,d] else error "arity"
apply5 p a b c d e = if fromMaybe 5 (arity p) == 5 then applyPredicate p [a,b,c,d,e] else error "arity"
apply6 p a b c d e f = if fromMaybe 6 (arity p) == 6 then applyPredicate p [a,b,c,d,e,f] else error "arity"
apply7 p a b c d e f g = if fromMaybe 7 (arity p) == 7 then applyPredicate p [a,b,c,d,e,f,g] else error "arity"
-}

showApply :: (HasPredicate atom p term, IsTerm term v f, Show v, Show p, Show f) => atom -> String
showApply =
    foldPredicate (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))")

prettyApply :: (HasPredicate atom p term, IsTerm term v f) => (v -> Doc) -> (p -> Doc) -> (f -> Doc) -> Int -> atom -> Doc
prettyApply pv pp pf _prec atom =
    foldPredicate (\ p ts ->
                   pp p <> case ts of
                             [] -> empty
                             _ -> parens (cat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
              atom

-- | Return the variables that occur in an instance of HasPredicate.
varApply :: (HasPredicate atom p term, IsTerm term v f) => atom -> Set.Set v
varApply = foldPredicate (\ _ args -> Set.unions (map fvt args))

substApply :: (HasPredicate atom p term, HasBoolean atom, IsTerm term v f) => Map.Map v term -> atom -> atom
substApply env = foldPredicate (\ p args -> apply p (map (tsubst env) args))

{-
instance (HasPredicate atom p term, Term term v f, HasBoolean atom) => Formula atom term v where
    allVariables = varApply
    freeVariables = varApply
    substitute = substApply
-}

pApp :: (IsFormula formula atom, HasPredicate atom p term) => p -> [term] -> formula
pApp p ts = atomic (applyPredicate p ts)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: (IsFormula formula atom, HasPredicate atom p term) => p -> formula
pApp0 p = pApp p []
pApp1 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> formula
pApp1 p a = pApp p [a]
pApp2 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> formula
pApp2 p a b = pApp p [a, b]
pApp3 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = pApp p [a, b, c]
pApp4 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = pApp p [a, b, c, d]
pApp5 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = pApp p [a, b, c, d, e]
pApp6 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = pApp p [a, b, c, d, e, f]
pApp7 :: (IsFormula formula atom, HasPredicate atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
pApp7 p a b c d e f g = pApp p [a, b, c, d, e, f, g]
