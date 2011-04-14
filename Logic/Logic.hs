-- | The Logic type class defines the basic boolean logic operations,
-- AND, OR, NOT, and so on.  Definitions which pertain to both
-- propositional and first order logic are here.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Logic
    ( Negatable(..)
    , Logic(..)
    , BinOp(..)
    , Boolean(..)
    , Combine(..)
    , combine
    ) where

import Data.Data (Data)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |The class of formulas that can be negated.  There are some types
-- that can be negated but do not support the other Boolean Logic
-- operators, such as the Literal class.
class Negatable formula where
    -- | Is this negated at the top level?
    negated :: formula -> Bool
    -- | Negation (This needs to check for and remove double negation)
    (.~.) :: formula -> formula

-- |A type class for logical formulas.  Minimal implementation:
-- @
--  (.|.), (.~.)
-- @
class Negatable formula => Logic formula where
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

-- | The 'BinOp' type (and in 'Logic.FirstOrder' the 'InfixPred' and
-- 'Quant' types) could be parameters of the type class instead of
-- being implemented here concretely, but I'm not sure whether the
-- added complexity is worthwhile.
data BinOp
    = (:<=>:)  -- ^ Equivalence
    |  (:=>:)  -- ^ Implication
    |  (:&:)  -- ^ AND
    |  (:|:)  -- ^ OR
    deriving (Eq,Ord,Read,Data,Typeable,Enum,Bounded)

data Combine formula
    = BinOp formula BinOp formula
    | (:~:) formula
    deriving (Eq,Ord,Read,Data,Typeable)

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

instance Show BinOp where
    show (:<=>:) = "(:<=>:)"
    show (:=>:) = "(:=>:)"
    show (:&:) = "(:&:)"
    show (:|:) = "(:|:)"

-- | A helper function for building folds:
-- @
--   foldF0 combine atomic
-- @
-- is a no-op
combine :: Logic formula => Combine formula -> formula
combine (BinOp f1 (:<=>:) f2) = f1 .<=>. f2
combine (BinOp f1 (:=>:) f2) = f1 .=>. f2
combine (BinOp f1 (:&:) f2) = f1 .&. f2
combine (BinOp f1 (:|:) f2) = f1 .|. f2
combine ((:~:) f) = (.~.) f

instance Version BinOp
instance Version (Combine formula)

-- |For some functions the atomic predicate type needs to have True
-- and False elements.
class Boolean p where
    fromBool :: Bool -> p

$(deriveSerialize ''BinOp)
$(deriveSerialize ''Combine)

$(deriveNewData [''BinOp, ''Combine])
