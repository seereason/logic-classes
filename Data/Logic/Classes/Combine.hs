-- | Class Logic defines the basic boolean logic operations,
-- AND, OR, NOT, and so on.  Definitions which pertain to both
-- propositional and first order logic are here.
{-# LANGUAGE DeriveDataTypeable #-}
module Data.Logic.Classes.Combine
    ( Combinable(..)
    , Combine(..)
    , combine
    , BinOp(..)
    , binop
    -- * Unicode aliases for Combinable class methods
    , (∧)
    , (∨)
    , (⇒)
    , (⇔)
    -- * Use in Harrison's code
    , (==>)
    , (<=>)
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Negate (Negatable(..))

-- |A type class for logical formulas.  Minimal implementation:
-- @
--  (.|.), (.~.)
-- @
class (Constants formula, Negatable formula, Ord formula) => Combinable formula where
    -- | Disjunction/OR
    (.|.) :: formula -> formula -> formula

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

-- |'Combine' is a helper type used in the signatures of the
-- 'foldPropositional' and 'foldFirstOrder' methods so can represent
-- all the ways that formulas can be combined using boolean logic -
-- negation, logical And, and so forth.
data Combine formula
    = BinOp formula BinOp formula
    | (:~:) formula
    deriving (Eq,Ord,Data,Typeable)

-- |We need to implement read manually here due to
-- <http://hackage.haskell.org/trac/ghc/ticket/4136>
{-
instance Read BinOp where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:<=>:), ":<=>:"),
                 ((:=>:), ":=>:"),
                 ((:&:), ":&:"),
                 ((:|:), ":|:")]
-}

-- | A helper function for building folds:
-- @
--   foldPropositional combine atomic
-- @
-- is a no-op.
combine :: Combinable formula => Combine formula -> formula
combine (BinOp f1 (:<=>:) f2) = f1 .<=>. f2
combine (BinOp f1 (:=>:) f2) = f1 .=>. f2
combine (BinOp f1 (:&:) f2) = f1 .&. f2
combine (BinOp f1 (:|:) f2) = f1 .|. f2
combine ((:~:) f) = (.~.) f

-- | Represents the boolean logic binary operations, used in the
-- Combine type above.
data BinOp
    = (:<=>:)  -- ^ Equivalence
    |  (:=>:)  -- ^ Implication
    |  (:&:)  -- ^ AND
    |  (:|:)  -- ^ OR
    deriving (Eq,Ord,Data,Typeable,Enum,Bounded)

binop :: Combinable formula => formula -> BinOp -> formula -> formula
binop a (:&:) b = a .&. b
binop a (:|:) b = a .|. b
binop a (:=>:) b = a .=>. b
binop a (:<=>:) b = a .<=>. b

(∧) :: Combinable formula => formula -> formula -> formula
(∧) = (.&.)
(∨) :: Combinable formula => formula -> formula -> formula
(∨) = (.|.)
-- | ⇒ can't be a function when -XUnicodeSyntax is enabled.
(⇒) :: Combinable formula => formula -> formula -> formula
(⇒) = (.=>.)
(⇔) :: Combinable formula => formula -> formula -> formula
(⇔) = (.<=>.)

(==>) :: Combinable formula => formula -> formula -> formula
(==>) = (.=>.)
(<=>) :: Combinable formula => formula -> formula -> formula
(<=>) = (.<=>.)
