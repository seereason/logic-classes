{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
module Data.Logic.Instances.TPTP where

import Codec.TPTP (F(..), Formula, BinOp(..), V(..), T(..), Term0(..), AtomicWord(..), Formula0(..), InfixPred(..))
import qualified Codec.TPTP as TPTP
import Control.Monad.Identity (Identity(..))
import Data.Char (isDigit, ord)
import Data.Generics (Data, Typeable)
import Data.Set (member)
import Data.String (IsString(..))
import FOL (IsFirstOrder(..), IsPredicate(..), IsTerm(..), IsVariable(variant), pApp)
import Pretty (Pretty(..))
import Prop (IsPropositional(..))
import Skolem (HasSkolem(..))
import Formulas (IsNegatable(..))
import Text.PrettyPrint (text)

-- |Generate a series of variable names.
instance IsVariable V where
    -- one = V "VS1"
    variant x@(V s) xs = if member x xs then variant (V (next s)) xs else x
        where
          next s = case break (not . isDigit) (reverse s) of
                     ("", "SV") -> "VS1"
                     (digits, "SV") -> "VS" ++ show (1 + read (reverse digits) :: Int)
                     _ -> "VS1"

instance Pretty V where
    pPrint (V s) = text s

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

instance HasSkolem AtomicFunction where
    type SVarOf AtomicFunction = V
    toSkolem = Skolem . V . ("sK" ++) . show
    -- fromSkolem (Skolem (V s)) = Just (read (drop 2 s) :: Int)
    -- fromSkolem _ = Nothing

{-
-- |This is not a safe way to implement booleans.
instance Data.Logic.Boolean AtomicWord where
    fromBool = AtomicWord . show
-}

instance Pretty AtomicFunction where
    pPrint (Atom w) = pPrint w
    pPrint (StringLit s) = text s
    pPrint (NumberLit n) = text (show n)
    pPrint (Skolem (V s)) = text ("sK" ++ s)

instance Pretty AtomicWord where
    pPrint (AtomicWord s) = text s

instance IsNegatable Formula where
    naiveNegate = F
    foldNegation' ne ther 
    negated _ = False
    (.~.) (F (Identity ((:~:) x))) = x
    (.~.) x   = (.~.) x

-- |If this looks confusing, it is because TPTP has the same operators
-- as Logic, the .&. on the left is the Logic method name and .&. on
-- the right is the TPTP function.
instance Data.Logic.Logic Formula where
    x .<=>. y = x .<=>. y
    x .=>.  y = x .=>. y
    x .<=.  y = x .<=. y
    x .|.   y = x .|. y
    x .&.   y = x .&. y
    x .<~>. y = x .<~>. y
    x .~|.  y = x .~|. y
    x .~&.  y = x .~&. y

-- |For types designed to represent first order (predicate) logic, it
-- is easiest to make the atomic type the same as the formula type,
-- and then raise an error if we see unexpected non-atomic formulas.
instance Data.Logic.PropositionalFormula Formula Formula where
    atomic (F (Identity (InfixPred t1 (:=:) t2))) = t1 .=. t2
    atomic (F (Identity (InfixPred t1 (:!=:) t2))) = t1 .!=. t2
    atomic (F (Identity (PredApp p ts))) = pApp p ts
    atomic _ = error "atomic method of PropositionalFormula for TPTP: invalid argument"
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF0 c a form =
        TPTP.foldF n' q' b' i' p' (unwrapF' form)
        where q' = error "TPTP Formula with quantifier passed to foldF0"
              n' f = c ((Logic.:~:) f)
              b' f1 (:<=>:) f2 = c (Logic.BinOp f1 (Logic.:<=>:) f2)
              b' f1 (:<=:) f2 = c (Logic.BinOp f2 (Logic.:=>:) f1)
              b' f1 (:=>:) f2 = c (Logic.BinOp f1 (Logic.:=>:) f2)
              b' f1 (:&:) f2 = c (Logic.BinOp f1 (Logic.:&:) f2)
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to use the equivalent ~(a&b)
              b' f1 (:~&:) f2 = TPTP.foldF n' q' b' i' p' ((.~.) (f1 .&. f2))
              b' f1 (:|:) f2 = c (Logic.BinOp f1 (Logic.:|:) f2)
              b' f1 (:~|:) f2 = TPTP.foldF n' q' b' i' p' ((.~.) (f1 .|. f2))
              b' f1 (:<~>:) f2 = TPTP.foldF n' q' b' i' p' ((((.~.) f1) .&. f2) .|. (f1 .&. ((.~.) f2)))
              i' t1 (:=:) t2 = a (F (Identity (InfixPred t1 (:=:) t2)))
              i' t1 (:!=:) t2 = a (F (Identity (InfixPred t1 (:!=:) t2)))
              p' p ts = a (F (Identity (PredApp p ts)))
              unwrapF' (F x) = F x -- copoint x

instance Data.Logic.FirstOrderFormula Formula (T Identity) V AtomicWord AtomicFunction where
    for_all vars x = for_all vars x
    exists vars x = exists vars x
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF q c p form =
        TPTP.foldF n' q' b' i' p' (unwrapF' form)
        where q' op (v:vs) form' =
                  let op' = case op of
                              TPTP.All -> Logic.All
                              TPTP.Exists -> Logic.Exists in
                  q op' v (foldr (\ v' f -> Logic.quant op' v' f) form' vs)
              q' _ [] form' = foldF q c p form'
              n' f = c ((Logic.:~:) f)
              b' f1 (:<=>:) f2 = c (Logic.BinOp f1 (Logic.:<=>:) f2)
              b' f1 (:<=:) f2 = c (Logic.BinOp f2 (Logic.:=>:) f1)
              b' f1 (:=>:) f2 = c (Logic.BinOp f1 (Logic.:=>:) f2)
              b' f1 (:&:) f2 = c (Logic.BinOp f1 (Logic.:&:) f2)
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to somehow use the equivalent ~(a&b)
              b' f1 (:~&:) f2 = TPTP.foldF n' q' b' i' p' ((.~.) (f1 .&. f2))
              b' f1 (:|:) f2 = c (Logic.BinOp f1 (Logic.:|:) f2)
              b' f1 (:~|:) f2 = TPTP.foldF n' q' b' i' p' ((.~.) (f1 .|. f2))
              b' f1 (:<~>:) f2 = TPTP.foldF n' q' b' i' p' ((((.~.) f1) .&. f2) .|. (f1 .&. ((.~.) f2)))
              i' t1 (:=:) t2 = p (Equal t1 t2)
              i' t1 (:!=:) t2 = p (NotEqual t1 t2) -- TPTP.foldF n' q' b' i' p' ((.~.) (t1 .=. t2))
              p' pr ts = p (Apply pr ts)
              unwrapF' (F x) = F x -- copoint x
    zipF = error "FIXME: Logic.Instances.TPTP.zipF"
    x .=. y   = x .=. y
    x .!=. y  = x .!=. y
    pApp0 p = TPTP.pApp p []
    pApp1 p a = TPTP.pApp p [a]
    pApp2 p a b = TPTP.pApp p [a,b]
    pApp3 p a b c = TPTP.pApp p [a,b,c]
    pApp4 p a b c d = TPTP.pApp p [a,b,c,d]
    pApp5 p a b c d e = TPTP.pApp p [a,b,c,d,e]
    pApp6 p a b c d e f = TPTP.pApp p [a,b,c,d,e,f]
    pApp7 p a b c d e f g = TPTP.pApp p [a,b,c,d,e,f,g]

instance (Eq AtomicFunction, Logic.Skolem AtomicFunction) => Data.Logic.Term (T Identity) V AtomicFunction where
    foldT v fa term =
        -- We call the foldT function from the TPTP package here, which
        -- has a different signature from the foldT method we are
        -- implementing.  The two extra term types in TPTP are represented
        -- here as additional values in the AtomicFunction type.
        TPTP.foldT string double v atom (unwrapT' term)
        where atom w ts = fa (Atom w) ts
              string s = fa (StringLit s) []
              double n = fa (NumberLit n) []
              unwrapT' (T x) = T x -- copoint x
    zipT = error "FIXME: Logic.Instances.TPTP.zipT"
    var = var
    fApp x args = 
        case x of
          Atom w -> TPTP.fApp w args
          StringLit s -> T {runT = Identity (DistinctObjectTerm s)}
          NumberLit n -> T {runT = Identity (NumberLitTerm n)}
          Skolem (V s) -> TPTP.fApp (AtomicWord ("Sk(" ++ s ++ ")")) args

--deriving instance Show TPTP.Term
--deriving instance (Show t, Show f) => Show (TPTP.Formula0 t f)
--deriving instance Show t => Show (TPTP.Term0 t)
