{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
module Logic.Instances.TPTP where

import Control.Monad.Identity (Identity(..))
-- import Codec.TPTP hiding (toTPTP)
import qualified Codec.TPTP as TPTP -- hiding (toTPTP)
import Data.String (IsString(fromString))
import qualified Logic.Class as Logic

-- |TPTP's Term type has two extra constructors that can be represented
-- using this augmented atomic function application type.
data AtomicFunction
    = Atom TPTP.AtomicWord 
    | StringLit String
    | NumberLit Double
    deriving Show

instance IsString AtomicFunction where
    fromString s = Atom (fromString s)

data AtomicFormula term v p f
    = InfixPred' term TPTP.InfixPred term
    | PredApp' p [term]
      deriving Show

type Atom = AtomicFormula TPTP.Term TPTP.V TPTP.AtomicWord AtomicFunction

instance Logic.PropositionalLogic TPTP.Formula Atom where
    x .<=>. y = x TPTP..<=>. y
    x .=>.  y = x TPTP..=>. y
    x .<=.  y = x TPTP..<=. y
    x .|.   y = x TPTP..|. y
    x .&.   y = x TPTP..&. y
    x .<~>. y = x TPTP..<~>. y
    x .~|.  y = x TPTP..~|. y
    x .~&.  y = x TPTP..~&. y
    (.~.) x   = (TPTP..~.) x 
    atomic (InfixPred' t1 (TPTP.:=:) t2) = (TPTP..=.) t1 t2
    atomic (InfixPred' t1 (TPTP.:!=:) t2) = (TPTP..!=.) t1 t2
    atomic (PredApp' p ts) = TPTP.pApp p ts
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF0 n b a formula =
        TPTP.foldF n q' b' i' p' (unwrapF' formula)
        where q' = error "TPTP Formula with quantifier passed to foldF0"
              b' f1 (TPTP.:<=>:) f2 = b f1 (Logic.:<=>:) f2
              b' f1 (TPTP.:<=:) f2 = b f2 (Logic.:=>:) f1
              b' f1 (TPTP.:=>:) f2 = b f1 (Logic.:=>:) f2
              b' f1 (TPTP.:&:) f2 = b f1 (Logic.:&:) f2
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to somehow use the equivalent ~(a&b)
              b' f1 (TPTP.:~&:) f2 = TPTP.foldF n q' b' i' p' ((TPTP..~.) ((TPTP..&.) f1 f2))
              b' f1 (TPTP.:|:) f2 = b f1 (Logic.:|:) f2
              b' f1 (TPTP.:~|:) f2 = TPTP.foldF n q' b' i' p' ((TPTP..~.) ((TPTP..|.) f1 f2))
              b' f1 (TPTP.:<~>:) f2 = TPTP.foldF n q' b' i' p' ((TPTP..|.) ((TPTP..&.) ((TPTP..~.) f1) f2) ((TPTP..&.) f1 ((TPTP..~.) f2)))
              i' t1 (TPTP.:=:) t2 = a (InfixPred' t1 (TPTP.:=:) t2)
              i' t1 (TPTP.:!=:) t2 = a (InfixPred' t1 (TPTP.:!=:) t2)
              p' p ts = a (PredApp' p ts)
              unwrapF' (TPTP.F x) = TPTP.F x -- copoint x

instance Logic.FirstOrderLogic TPTP.Formula Atom TPTP.Term TPTP.V TPTP.AtomicWord AtomicFunction where
    for_all vars x = TPTP.for_all vars x
    exists vars x = TPTP.exists vars x
    -- Use the TPTP fold to implement the Logic fold.  This means
    -- building wrappers around some of the functions so that when
    -- the wrappers are passed TPTP types they turn them into Logic
    -- values to pass to the argument functions.
    foldF n q b i p formula =
        TPTP.foldF n q' b' i' p (unwrapF' formula)
        where q' TPTP.All = q Logic.All
              q' TPTP.Exists = q Logic.Exists
              b' f1 (TPTP.:<=>:) f2 = b f1 (Logic.:<=>:) f2
              b' f1 (TPTP.:<=:) f2 = b f2 (Logic.:=>:) f1
              b' f1 (TPTP.:=>:) f2 = b f1 (Logic.:=>:) f2
              b' f1 (TPTP.:&:) f2 = b f1 (Logic.:&:) f2
              -- The :~&: operator is not present in the Logic BinOp type,
              -- so we need to somehow use the equivalent ~(a&b)
              b' f1 (TPTP.:~&:) f2 = TPTP.foldF n q' b' i' p ((TPTP..~.) ((TPTP..&.) f1 f2))
              b' f1 (TPTP.:|:) f2 = b f1 (Logic.:|:) f2
              b' f1 (TPTP.:~|:) f2 = TPTP.foldF n q' b' i' p ((TPTP..~.) ((TPTP..|.) f1 f2))
              b' f1 (TPTP.:<~>:) f2 = TPTP.foldF n q' b' i' p ((TPTP..|.) ((TPTP..&.) ((TPTP..~.) f1) f2) ((TPTP..&.) f1 ((TPTP..~.) f2)))
              i' t1 (TPTP.:=:) t2 = i t1 (Logic.:=:) t2
              i' _t1 (TPTP.:!=:) _t2 = undefined
              unwrapF' (TPTP.F x) = TPTP.F x -- copoint x
    foldT v fa term =
        -- The two extra term types in TPTP are represented here as
        -- additional values in the AtomicFunction type.
        TPTP.foldT string double v atom (unwrapT' term)
        where atom w ts = fa (Atom w) ts
              string s = fa (StringLit s) []
              double n = fa (NumberLit n) []
              unwrapT' (TPTP.T x) = TPTP.T x -- copoint x
    x .=. y   = x TPTP..=. y
    x .!=. y  = x TPTP..!=. y
    pApp x args = TPTP.pApp x args
    var = TPTP.var
    fApp x args = 
        case x of
          Atom w -> TPTP.fApp w args
          StringLit s -> TPTP.T {TPTP.runT = Identity (TPTP.DistinctObjectTerm s)}
          NumberLit n -> TPTP.T {TPTP.runT = Identity (TPTP.NumberLitTerm n)}
    toString (TPTP.V s) = s

{-
-- Formulae whose subexpressions are wrapped in the given type constructor @c@.
instance Logic.Formulae (TPTP.F c) (TPTP.T c) TPTP.V TPTP.AtomicWord AtomicFunction where
    for_all vars x = TPTP.for_all vars x
    exists vars x = TPTP.exists vars x
    x .<=>. y = x TPTP..<=>. y
    x .=>.  y = x TPTP..=>. y
    x .<=.  y = x TPTP..<=. y
    x .|.   y = x TPTP..|. y
    x .&.   y = x TPTP..&. y
    x .<~>. y = x TPTP..<~>. y
    x .~|.  y = x TPTP..~|. y
    x .~&.  y = x TPTP..~&. y
    (.~.) x   = (TPTP..~.) x 
    -- * Formula Builders
    x .=. y   = x TPTP..=. y
    x .!=. y  = x TPTP..!=. y
    pApp x args = TPTP.pApp x args
    var = TPTP.var
    fApp x args = 
        case x of
          Atom w -> TPTP.fApp w args
          StringLit s -> TPTP.T {TPTP.runT = Identity (TPTP.DistinctObjectTerm s)}
          NumberLit n -> TPTP.T {TPTP.runT = Identity (TPTP.NumberLitTerm n)}
    foldF neg quant bin inf pred formula =
        TPTP.foldF neg quant' bin' inf' pred (unwrapF formula)
        where quant' TPTP.All = quant Logic.All
              quant' TPTP.Exists = quant Logic.Exists
              bin' f1 (TPTP.:<=>:) f2 = bin f1 (Logic.:<=>:) f2
              inf' t1 (TPTP.:=:) t2 = inf t1 (Logic.:=:) t2
    -- 
    foldT v fa term =
        -- The two extra term types in TPTP are represented here as
        -- additional values in the AtomicFunction type.
        TPTP.foldT string double v atom (unwrapT term)
        where atom w ts = fa (Atom w) ts
              string s = fa (StringLit s) []
              double n = fa (NumberLit n) []
    toString (TPTP.V s) = s
-}

unwrapF (TPTP.F x) = TPTP.copoint x
unwrapT (TPTP.T x) = TPTP.copoint x

-- toTPTP :: Logic.Formulae formula term v p f -> TPTPFormula
-- |Convert any instance of Formulae into Formula
toTPTP :: Logic.FirstOrderLogic formula atom term v p f => formula -> TPTP.Formula
toTPTP formula = 
    Logic.foldF n q b i p formula
    where
      n f = (TPTP..~.) (toTPTP f) :: TPTP.Formula
      q Logic.All vs f = TPTP.for_all (map (fromString . Logic.toString) vs) (toTPTP f)
      q Logic.Exists vs f = TPTP.exists (map (fromString . Logic.toString) vs) (toTPTP f)
      b = undefined
      i = undefined
      p = undefined
