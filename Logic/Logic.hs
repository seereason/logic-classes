-- | The Logic type class defines the basic boolean logic operations,
-- AND, OR, NOT, and so on.  Definitions which pertain to both
-- propositional and first order logic are here.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Logic
    ( Logic(..)
    , BinOp(..)
    , binOp
    , Boolean(..)
    ) where

import Data.Data (Data)
import Data.List (isPrefixOf)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |A type class for logical formulas.  Minimal implementation:
-- @
--  (.|.), (.~.)
-- @
class Logic formula where
    -- | Disjunction/OR
    (.|.) :: formula -> formula -> formula
    -- | Negation
    (.~.) :: formula -> formula

    -- | Derived formula combinators.  These could (and should!) be
    -- overridden with expressions native to the instance.
    --
    -- | Conjunction/AND
    (.&.) :: formula -> formula -> formula
    x .&. y = (.~.) ((.~.) x .|. (.~.) y)
    -- | Formula combinators: Equivalence
    (.<=>.) :: formula -> formula -> formula
    x .<=>. y = (x .=>. y) .&. (y .=>. x)
    -- | Implication
    (.=>.) :: formula -> formula -> formula
    x .=>. y = ((.~.) x .|. y)
    -- | Reverse implication:
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

infixl 2  .<=>. ,  .=>. ,  .<~>.
infixl 3  .&.
infixl 4  .|.  -- a & b | c means a & (b | c), which in cnf would be [[a], [b, c]]

-- | The 'BinOp' type (and in 'Logic.FirstOrder' the 'InfixPred' and
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

-- | A helper function for building folds:
-- @
--   foldF0 (.~.) binOp atomic
-- @
-- is a no-op
binOp :: Logic formula => formula -> BinOp -> formula -> formula
binOp f1 (:<=>:) f2 = f1 .<=>. f2
binOp f1 (:=>:) f2 = f1 .=>. f2
binOp f1 (:&:) f2 = f1 .&. f2
binOp f1 (:|:) f2 = f1 .|. f2

instance Version BinOp

-- |For some functions the atomic predicate type needs to have True
-- and False elements.
class Boolean p where
    fromBool :: Bool -> p

$(deriveSerialize ''BinOp)

$(deriveNewData [''BinOp])
