{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
module Logic.Instances.TPTP where

import Control.Monad.Identity (Identity(..))
import Codec.TPTP
import Data.Char (isDigit, ord, chr)
import Data.Generics (Data, Typeable)
import Data.String (IsString(..))
import qualified Logic.FirstOrder as Logic
import qualified Logic.Logic as Logic
import qualified Logic.Propositional as Logic
import Text.PrettyPrint (text)

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

instance Logic.Pretty V where
    pretty (V s) = text s

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
    | Skolem V
    deriving (Eq, Ord, Show, Data, Typeable)

instance IsString AtomicFunction where
    fromString = Atom . AtomicWord

instance Logic.Skolem AtomicFunction where
    toSkolem = Skolem . V . ("sK" ++) . show
    fromSkolem (Skolem (V s)) = Just (read (drop 2 s) :: Int)
    fromSkolem _ = Nothing

-- |This is not a safe way to implement booleans.
instance Logic.Boolean AtomicWord where
    fromBool flag = AtomicWord (show flag)

instance Logic.Pretty AtomicFunction where
    pretty (Atom w) = Logic.pretty w
    pretty (StringLit s) = text (show s)
    pretty (NumberLit n) = text (show n)
    pretty (Skolem (V s)) = text ("Sk" ++ s)

instance Logic.Pretty AtomicWord where
    pretty (AtomicWord s) = text s

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

instance (Eq AtomicFunction, Logic.Skolem AtomicFunction) => Logic.FirstOrderLogic Formula Term V AtomicWord AtomicFunction where
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
    zipF = error "Unimplemented: Logic.Instances.TPTP.zipF"
    x .=. y   = x .=. y
    x .!=. y  = x .!=. y
    pApp x args = pApp x args

instance (Eq AtomicFunction, Logic.Skolem AtomicFunction) => Logic.Term Term V AtomicFunction where
    foldT v fa term =
        -- We call the foldT function from the TPTP package here, which
        -- has a different signature from the foldT method we are
        -- implementing.  The two extra term types in TPTP are represented
        -- here as additional values in the AtomicFunction type.
        foldT string double v atom (unwrapT' term)
        where atom w ts = fa (Atom w) ts
              string s = fa (StringLit s) []
              double n = fa (NumberLit n) []
              unwrapT' (T x) = T x -- copoint x
    zipT = error "Unimplemented: Logic.Instances.TPTP.zipT"
    var = var
    fApp x args = 
        case x of
          Atom w -> fApp w args
          StringLit s -> T {runT = Identity (DistinctObjectTerm s)}
          NumberLit n -> T {runT = Identity (NumberLitTerm n)}
          Skolem (V s) -> fApp (AtomicWord ("Sk(" ++ s ++ ")")) args
