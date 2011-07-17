{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Predicate
    ( Arity(..)
    , Pred(..)
    , pApp
    , Predicate(..)
    ) where

import Data.Data (Data)
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Data.Logic.Logic (Boolean(fromBool), Negatable((.~.)), Logic)

class Arity p where
    -- |How many arguments does the predicate take?  Nothing
    -- means any number of arguments.
    arity :: p -> Maybe Int

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

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldF and makes it easier to manage the
-- mapping of the different instances to the class methods.
data Predicate p term
    = Equal term term
    | NotEqual term term
    | Constant Bool
    | Apply p [term]
    deriving (Eq, Ord, Show, Read, Data, Typeable)

$(deriveSafeCopy 1 'base ''Predicate)

$(deriveNewData [''Predicate])
