-- | PropositionalLogic is a multi-parameter type class for
-- representing instance of propositional (aka zeroth order) logic
-- datatypes.  These are formulas which have truth values, but no "for
-- all" or "there exists" quantifiers and thus no variables or terms
-- as we have in first order or predicate logic.  It is intended that
-- we will be able to write instances for various different
-- implementations to allow these systems to interoperate.  The
-- operator names were adopted from the Logic-TPTP package.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Propositional
    ( PropositionalLogic(..)
    , BinOp(..)
    , binOp
    , showForm0
    , convertProp
    ) where

import Data.Data (Data)
import Data.List (isPrefixOf)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |The type class.  Minimal implementation:
-- @
--  (.<=>.), (.=>.), (.|.), (.&.), (.~.), foldF0
-- @
class Show atom => PropositionalLogic formula atom | formula -> atom where
    -- | Formula combinators: Equivalence
    (.<=>.) :: formula -> formula -> formula
    -- | Implication
    (.=>.) :: formula -> formula -> formula
    -- | Disjunction/OR
    (.|.) :: formula -> formula -> formula
    -- | Conjunction/AND
    (.&.) :: formula -> formula -> formula
    -- | Negation
    (.~.) :: formula -> formula
    -- | Build an atomic formula from the atom type.
    atomic :: atom -> formula
    -- | A fold function that distributes different sorts of formula
    -- to its parameter functions, one to handle binary operators, one
    -- for negations, and one for atomic formulas.  See examples of its
    -- use to implement the polymorphic functions below.
    foldF0 :: (formula -> r)
           -> (formula -> BinOp -> formula -> r)
           -> (atom -> r)
           -> formula
           -> r

    -- | Derived formula combinators.  These could be overridden for instances
    -- that actually have constructors to represent them, such as Logic-TPTP.
    -- Reverse implication:
    (.<=.) :: formula -> formula -> formula
    x .<=. y = y .=>. x
    -- | Exclusive or
    (.<~>.) :: formula -> formula -> formula
    x .<~>. y = ((.~.) x .&. y) .|. (x .&. (.~.) y)
    -- | Nor
    (.~|.) :: formula -> formula -> formula
    x .~|. y = (.~.) (x .|. y)
    -- | Nand
    (.~&.) :: formula -> formula -> formula
    x .~&. y = (.~.) (x .&. y)

-- | A helper function for building folds:
-- @
--   foldF0 (.~.) binOp atomic
-- @
-- is a no-op
binOp :: PropositionalLogic formula atom => formula -> BinOp -> formula -> formula
binOp f1 (:<=>:) f2 = f1 .<=>. f2
binOp f1 (:=>:) f2 = f1 .=>. f2
binOp f1 (:&:) f2 = f1 .&. f2
binOp f1 (:|:) f2 = f1 .|. f2

-- | Show a formula in a format that can be evaluated 
showForm0 :: PropositionalLogic formula atom => formula -> String
showForm0 formula =
    foldF0 n b a formula
    where
      n f = "(.~.) " ++ parenForm f
      b f1 op f2 = parenForm f1 ++ " " ++ showFormOp op ++ " " ++ parenForm f2
      a atom = "atom " ++ show atom
      parenForm x = "(" ++ showForm0 x ++ ")"
      showFormOp (:<=>:) = ".<=>."
      showFormOp (:=>:) = ".=>."
      showFormOp (:&:) = ".&."
      showFormOp (:|:) = ".|."

infixl 2  .<=>. ,  .=>. ,  .<~>.
infixl 3  .|.
infixl 4  .&.

-- | The 'BinOp' type (and in 'Logic.Predicate' the 'InfixPred' and
-- 'Quant' types) could be parameters of the type class instead of
-- being implemented here concretely, but I'm not sure whether the
-- added complexity is worthwhile.
data BinOp
    = (:<=>:)  -- ^ Equivalence
    |  (:=>:)  -- ^ Implication
    |  (:&:)  -- ^ AND
    |  (:|:)  -- ^ OR
    deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- <http://hackage.haskell.org/trac/ghc/ticket/4136>
instance Read BinOp where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:<=>:), ":<=>:"),
                 ((:=>:), ":=>:"),
                 ((:&:), ":&:"),
                 ((:|:), ":|:")]

-- |Convert any instance of a propositional logic expression to any
-- other using the supplied atom conversion function.
convertProp :: forall formula1 atom1 formula2 atom2.
               (PropositionalLogic formula1 atom1,
                PropositionalLogic formula2 atom2) =>
               (atom1 -> atom2) -> formula1 -> formula2
convertProp convertA formula =
    foldF0 n b a formula
    where
      convert' = convertProp convertA
      n f = (.~.) (convert' f)
      b f1 op f2 = binOp (convert' f1) op (convert' f2)
      a = atomic . convertA

instance Version BinOp

$(deriveSerialize ''BinOp)

$(deriveNewData [''BinOp])
