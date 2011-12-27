{-# LANGUAGE FlexibleContexts, FunctionalDependencies, MultiParamTypeClasses, TypeFamilies #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- | The Atom class represents the application of an atomic predicate
-- to zero or more terms.
module Data.Logic.Classes.Atom
    ( Atom(..)
    , apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7
    ) where

import Data.Logic.Classes.Arity
import Data.Logic.Classes.Constants
--import Data.Logic.Classes.Term
import Data.Maybe (fromMaybe)

class (Arity p, Constants p, Eq p) => Atom atom p term | atom -> p term, term -> atom p where
    foldAtom :: (p -> [term] -> r) -> (Bool -> r) -> atom -> r
    zipAtoms :: (p -> [term] -> p -> [term] -> Maybe r) -> (Bool -> Bool -> Maybe r) -> atom -> atom -> Maybe r
    apply' :: p -> [term] -> atom
    -- | apply' with an arity check - clients should always call this.
    apply :: p -> [term] -> atom
    apply p ts =
        case arity p of
          Just n | n /= length ts -> error "arity"
          _ -> apply' p ts

apply0 p = if fromMaybe 0 (arity p) == 0 then apply' p [] else error "arity"
apply1 p a = if fromMaybe 1 (arity p) == 1 then apply' p [a] else error "arity"
apply2 p a b = if fromMaybe 2 (arity p) == 2 then apply' p [a,b] else error "arity"
apply3 p a b c = if fromMaybe 3 (arity p) == 3 then apply' p [a,b,c] else error "arity"
apply4 p a b c d = if fromMaybe 4 (arity p) == 4 then apply' p [a,b,c,d] else error "arity"
apply5 p a b c d e = if fromMaybe 5 (arity p) == 5 then apply' p [a,b,c,d,e] else error "arity"
apply6 p a b c d e f = if fromMaybe 6 (arity p) == 6 then apply' p [a,b,c,d,e,f] else error "arity"
apply7 p a b c d e f g = if fromMaybe 7 (arity p) == 7 then apply' p [a,b,c,d,e,f,g] else error "arity"
