{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
module Logic.Instances.TPTP where

import Control.Monad.Identity (Identity(..))
import Codec.TPTP
import Data.Char (isDigit, ord, chr)
import Data.String (IsString(fromString))
import qualified Logic.Logic as Logic
import qualified Logic.Predicate as Logic

-- |Generate a series of variable names.  
instance Enum V where
    succ v =
        toEnum (if n < cnt then n + 1 else if n == cnt then ord pref + cnt else n + cnt)
            where n = fromEnum v
    fromEnum (V s) =
        case break (not . isDigit) (reverse s) of
          ("", [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn
          (n, [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn + cnt * (read (reverse n) :: Int)
          _ -> error $ "Invalid variable name: " ++ show s
    toEnum n =
        V (chr (ord mn + pre) : if suf == 0 then "" else show suf)
        where (suf, pre) = divMod n cnt

mn = 'x'
pref = 'x'
mx = 'z'
cnt = ord mx - ord mn + 1

-- |TPTP's Term type has two extra constructors that can be represented
-- using this augmented atomic function application type.
data AtomicFunction
    = Atom AtomicWord 
    | StringLit String
    | NumberLit Double
    deriving Show

instance IsString AtomicFunction where
    fromString s = Atom (fromString s)

-- |If this looks confusing, it is because TPTP has the same operators
-- as Logic, the .&. on the left is the Logic method name and .&. on
-- the right is the TPTP function.
instance Logic.Logic Formula where
    x .<=>. y = x .<=>. y
    x .=>.  y = x .=>. y
    x .<=.  y = x .<=. y
    x .|.   y = x .|. y
    x .&.   y = x .&. y
    x .<~>. y = x .<~>. y
    x .~|.  y = x .~|. y
    x .~&.  y = x .~&. y
    (.~.) x   = (.~.) x 

-- |For types designed to represent first order (predicate) logic, it
-- is easiest to make the atomic type the same as the formula type,
-- and then raise an error if we see unexpected non-atomic formulas.
instance Logic.PropositionalLogic Formula Formula where
    atomic (F (Identity (InfixPred t1 (:=:) t2))) = t1 .=. t2
    atomic (F (Identity (InfixPred t1 (:!=:) t2))) = t1 .!=. t2
    atomic (F (Identity (PredApp p ts))) = pApp p ts
    atomic _ = error "atomic method of PropositionalLogic for TPTP: invalid argument"
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF0 n b a form =
        foldF n q' b' i' p' (unwrapF' form)
        where q' = error "TPTP Formula with quantifier passed to foldF0"
              b' f1 (:<=>:) f2 = b f1 (Logic.:<=>:) f2
              b' f1 (:<=:) f2 = b f2 (Logic.:=>:) f1
              b' f1 (:=>:) f2 = b f1 (Logic.:=>:) f2
              b' f1 (:&:) f2 = b f1 (Logic.:&:) f2
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to somehow use the equivalent ~(a&b)
              b' f1 (:~&:) f2 = foldF n q' b' i' p' ((.~.) (f1 .&. f2))
              b' f1 (:|:) f2 = b f1 (Logic.:|:) f2
              b' f1 (:~|:) f2 = foldF n q' b' i' p' ((.~.) (f1 .|. f2))
              b' f1 (:<~>:) f2 = foldF n q' b' i' p' ((((.~.) f1) .&. f2) .|. (f1 .&. ((.~.) f2)))
              i' t1 (:=:) t2 = a (F (Identity (InfixPred t1 (:=:) t2)))
              i' t1 (:!=:) t2 = a (F (Identity (InfixPred t1 (:!=:) t2)))
              p' p ts = a (F (Identity (PredApp p ts)))
              unwrapF' (F x) = F x -- copoint x

instance Logic.PredicateLogic Formula Term V AtomicWord AtomicFunction where
    for_all vars x = for_all vars x
    exists vars x = exists vars x
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF n q b i p form =
        foldF n q' b' i' p (unwrapF' form)
        where q' All = q Logic.All
              q' Exists = q Logic.Exists
              b' f1 (:<=>:) f2 = b f1 (Logic.:<=>:) f2
              b' f1 (:<=:) f2 = b f2 (Logic.:=>:) f1
              b' f1 (:=>:) f2 = b f1 (Logic.:=>:) f2
              b' f1 (:&:) f2 = b f1 (Logic.:&:) f2
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to somehow use the equivalent ~(a&b)
              b' f1 (:~&:) f2 = foldF n q' b' i' p ((.~.) (f1 .&. f2))
              b' f1 (:|:) f2 = b f1 (Logic.:|:) f2
              b' f1 (:~|:) f2 = foldF n q' b' i' p ((.~.) (f1 .|. f2))
              b' f1 (:<~>:) f2 = foldF n q' b' i' p ((((.~.) f1) .&. f2) .|. (f1 .&. ((.~.) f2)))
              i' t1 (:=:) t2 = i t1 (Logic.:=:) t2
              i' _t1 (:!=:) _t2 = undefined
              unwrapF' (F x) = F x -- copoint x
    foldT v fa term =
        -- The two extra term types in TPTP are represented here as
        -- additional values in the AtomicFunction type.
        foldT string double v atom (unwrapT' term)
        where atom w ts = fa (Atom w) ts
              string s = fa (StringLit s) []
              double n = fa (NumberLit n) []
              unwrapT' (T x) = T x -- copoint x
    x .=. y   = x .=. y
    x .!=. y  = x .!=. y
    pApp x args = pApp x args
    var = var
    fApp x args = 
        case x of
          Atom w -> fApp w args
          StringLit s -> T {runT = Identity (DistinctObjectTerm s)}
          NumberLit n -> T {runT = Identity (NumberLitTerm n)}
    toString (V s) = s
