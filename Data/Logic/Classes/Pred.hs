{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, ScopedTypeVariables #-}
module Data.Logic.Classes.Pred where

import Data.Logic.Classes.Arity
import Data.Logic.Classes.Boolean
import Data.Logic.Classes.Logic
import Data.Logic.Classes.Negatable

-- |A class of predicates
class (Logic formula, Boolean p, Arity p) => Pred p term formula | formula -> p, formula -> term where
    pApp0 :: p  -> formula
    pApp1 :: p -> term -> formula
    pApp2 :: p -> term -> term -> formula
    pApp3 :: p -> term -> term -> term -> formula
    pApp4 :: p -> term -> term -> term -> term -> formula
    pApp5 :: p -> term -> term -> term -> term -> term -> formula
    pApp6 :: p -> term -> term -> term -> term -> term -> term -> formula
    pApp7 :: p -> term -> term -> term -> term -> term -> term -> term -> formula
    -- | Equality of Terms
    (.=.) :: term -> term -> formula
    -- | Inequality of Terms
    (.!=.) :: term -> term -> formula
    a .!=. b = (.~.) (a .=. b)
    -- | The tautological formula
    true :: formula
    true = pApp0 (fromBool True :: p)
    -- | The inconsistant formula
    false :: formula
    false = pApp0 (fromBool False :: p)

pApp :: (Pred p term formula, Arity p) => p -> [term] -> formula
pApp p ts =
    case (ts, maybe (length ts) id (arity p)) of
      ([], 0) -> pApp0 p 
      ([a], 1) -> pApp1 p a
      ([a,b], 2) -> pApp2 p a b
      ([a,b,c], 3) -> pApp3 p a b c
      ([a,b,c,d], 4) -> pApp4 p a b c d
      ([a,b,c,d,e], 5) -> pApp5 p a b c d e
      ([a,b,c,d,e,f], 6) -> pApp6 p a b c d e f
      ([a,b,c,d,e,f,g], 7) -> pApp7 p a b c d e f g
      _ -> error ("Arity error" {- ++ show (pretty p) ++ " " ++ intercalate " " (map (show . pretty) ts) -})
