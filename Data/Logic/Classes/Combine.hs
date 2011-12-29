-- | Class Logic defines the basic boolean logic operations,
-- AND, OR, NOT, and so on.  Definitions which pertain to both
-- propositional and first order logic are here.
{-# LANGUAGE DeriveDataTypeable #-}
module Data.Logic.Classes.Combine
    ( Combinable(..)
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
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Negate (Negatable(..))

-- | Abbreviation for the type signature passed to the fold function.
type CombineFold formula r =
       (formula -> BinOp -> formula -> r)
    -> (formula -> r)
    -> (Bool -> r)
    -> formula -> r

-- | Abbreviation for the type signature passed to the zip function.
type CombineZip formula r =
       (formula -> BinOp -> formula -> formula -> BinOp -> formula -> Maybe r)
    -> (formula -> formula -> Maybe r)
    -> (Bool -> Bool -> Maybe r)
    -> formula -> formula -> Maybe r

-- | A type class for logical formulas.  Minimal implementation:
-- @
--  (.|.)
-- @
class ({- Constants formula, -} Negatable formula) => Combinable formula where
    foldCombine :: CombineFold formula r
    zipCombines :: CombineZip formula r
    zipCombines bin neg tf fm1 fm2 =
        foldCombine bin2 neg2 tf2 fm2
        where
          bin2 p2 op2 q2 = foldCombine (\ p1 op1 q1 -> bin p1 op1 q1 p2 op2 q2)
                                       (\ _ -> Nothing)
                                       (\ _ -> Nothing)
                                       fm1
          neg2 p2 = foldCombine (\ _ _ _ -> Nothing)
                                (\ p1 -> neg p1 p2)
                                (\ _ -> Nothing)
                                fm1
          tf2 b2 = foldCombine (\ _ _ _ -> Nothing)
                               (\ _ -> Nothing)
                               (\ b1 -> tf b1 b2)
                               fm1
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

infixr 2  .<=>. ,  .=>. ,  .<~>.
-- We had been using a different precedence for & and |, I'm swapping
-- 3 and 4 here to match Harrison and Haskell (and I assume most other
-- languages.)  So a .|. b .&. c means a .|. (b .&. c).  And False &&
-- True || True is True.
infixl 3  .|.
infixl 4  .&.

-- |'Combination' is a helper type used in the signatures of the
-- 'foldPropositional' and 'foldFirstOrder' methods so can represent
-- all the ways that formulas can be combined using boolean logic -
-- negation, logical And, and so forth.
data Combination formula
    = BinOp formula BinOp formula
    | (:~:) formula
    deriving (Eq,Ord,Data,Typeable,Show)

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
combine :: Combinable formula => Combination formula -> formula
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
    deriving (Eq,Ord,Data,Typeable,Enum,Bounded,Show)

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
