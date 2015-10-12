-- | Class Logic defines the basic boolean logic operations,
-- AND, OR, NOT, and so on.  Definitions which pertain to both
-- propositional and first order logic are here.
{-# LANGUAGE DeriveDataTypeable #-}
module Data.Logic.Classes.Combine
    ( IsCombinable(..)
    , Combination(..)
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
    , prettyBinOp
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Negate (IsNegatable, (.~.))
import Data.Logic.Classes.Pretty (Pretty(pPrint))
import Text.PrettyPrint (Doc, text)

-- | A type class for logical formulas.  Minimal implementation:
-- @
--  (.|.)
-- @
class (IsNegatable formula) => IsCombinable formula where
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

infixl 1  .<=>. ,  .<~>., ⇔, <=>
infixr 2  .=>., ⇒, ==>
infixr 3  .|., ∨
infixl 4  .&., ∧

-- |'Combination' is a helper type used in the signatures of the
-- 'foldPropositional' and 'foldFirstOrder' methods so can represent
-- all the ways that formulas can be combined using boolean logic -
-- negation, logical And, and so forth.
data Combination formula
    = BinOp formula BinOp formula
    | (:~:) formula
    deriving (Eq, Ord, Data, Typeable)

instance Show formula => Show (Combination formula) where
    show ((:~:) f) = "(.~.) (" ++ show f ++ ")"
    show (BinOp f op g) = "(" ++ show f ++ ") " ++ show op ++ " (" ++ show g ++ ")"

-- | A helper function for building folds:
-- @
--   foldPropositional combine atomic
-- @
-- is a no-op.
combine :: IsCombinable formula => Combination formula -> formula
combine (BinOp f1 (:<=>:) f2) = f1 .<=>. f2
combine (BinOp f1 (:=>:) f2) = f1 .=>. f2
combine (BinOp f1 (:&:) f2) = f1 .&. f2
combine (BinOp f1 (:|:) f2) = f1 .|. f2
combine ((:~:) f) = (.~.) f

-- | Represents the boolean logic binary operations, used in the
-- Combination type above.
data BinOp
    = (:<=>:)  -- ^ Equivalence
    |  (:=>:)  -- ^ Implication
    |  (:&:)  -- ^ AND
    |  (:|:)  -- ^ OR
    deriving (Eq, Ord, Data, Typeable, Enum, Bounded)

instance Show BinOp where
    show (:|:) = ".|."
    show (:&:) = ".&."
    show (:<=>:) = ".<=>."
    show (:=>:) = ".=>."

binop :: IsCombinable formula => formula -> BinOp -> formula -> formula
binop a (:&:) b = a .&. b
binop a (:|:) b = a .|. b
binop a (:=>:) b = a .=>. b
binop a (:<=>:) b = a .<=>. b

(∧) :: IsCombinable formula => formula -> formula -> formula
(∧) = (.&.)
(∨) :: IsCombinable formula => formula -> formula -> formula
(∨) = (.|.)
-- | ⇒ can't be a function when -XUnicodeSyntax is enabled.
(⇒) :: IsCombinable formula => formula -> formula -> formula
(⇒) = (.=>.)
(⇔) :: IsCombinable formula => formula -> formula -> formula
(⇔) = (.<=>.)

(==>) :: IsCombinable formula => formula -> formula -> formula
(==>) = (.=>.)
(<=>) :: IsCombinable formula => formula -> formula -> formula
(<=>) = (.<=>.)

prettyBinOp :: BinOp -> Doc
prettyBinOp (:<=>:) = text "⇔"
prettyBinOp (:=>:) = text "⇒"
prettyBinOp (:&:) = text "∧"
prettyBinOp (:|:) = text "∨"

instance Pretty BinOp where
    pPrint = prettyBinOp
