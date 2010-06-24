{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Propositional
    ( PropositionalLogic(..)
    , BinOp(..)
    , convertProp
    ) where

import Data.Data (Data)
import Data.List (isPrefixOf)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |PropositionalLogic is a multi-parameter type class for
-- representing order zero logic datatypes.  It is intended that we
-- will be able to write instances for various different
-- implementations to allow these systems to interoperate.  The class
-- is patterned on the type in the Logic-TPTP package.
class Show atom => PropositionalLogic formula atom | formula -> atom where
    (.<=>.) :: formula -> formula -> formula -- ^ Equivalence
    (.=>.) :: formula -> formula -> formula  -- ^ Implication
    (.<=.) :: formula -> formula -> formula  -- ^ Reverse implication
    x .<=. y = y .=>. x
    (.|.) :: formula -> formula -> formula   -- ^ Disjunction/OR
    (.&.) :: formula -> formula -> formula   -- ^ Conjunction/AND
    (.<~>.) :: formula -> formula -> formula -- ^ XOR
    x .<~>. y = ((.~.) x .&. y) .|. (x .&. (.~.) y)
    (.~|.) :: formula -> formula -> formula  -- ^ NOR
    x .~|. y = (.~.) (x .|. y)
    (.~&.) :: formula -> formula -> formula  -- ^ NAND
    x .~&. y = (.~.) (x .&. y)
    (.~.) :: formula -> formula                  -- ^ Negation
    -- Helper functions for building folds: foldF (.~.) quant binOp infixPred pApp is a no-op
    binOp :: formula -> BinOp -> formula -> formula
    binOp f1 (:<=>:) f2 = f1 .<=>. f2
    binOp f1 (:=>:) f2 = f1 .=>. f2
    -- binOp f1 (:<=:) f2 = f1 .<=. f2
    binOp f1 (:&:) f2 = f1 .&. f2
    binOp f1 (:|:) f2 = f1 .|. f2
    -- binOp f1 (:~&:) f2 = f1 .~&. f2
    -- binOp f1 (:~|:) f2 = f1 .~|. f2
    -- binOp f1 (:<~>:) f2 = f1 .<~>. f2
    atomic :: atom -> formula
    foldF0 :: (formula -> r)                        -- ^ Negation
           -> (formula -> BinOp -> formula -> r)    -- ^ Binary Operator
           -> (atom -> r)                           -- ^ Atomic formula
           -> formula
           -> r                                           -- ^ Fold over the value of a formula
    showForm0 :: formula -> String
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

-- * These three simple types could be parameters to the type class as
-- well instead of being implemented here concretely, but I'm not sure
-- whether the added complexity is worthwhile.

-- | Binary formula connectives 
data BinOp =
               (:<=>:)  -- ^ Equivalence
            |  (:=>:)  -- ^ Implication
            -- |  (:<=:)  -- ^ Reverse Implication
            |  (:&:)  -- ^ AND
            |  (:|:)  -- ^ OR
            -- |  (:~&:)  -- ^ NAND
            -- |  (:~|:)  -- ^ NOR
            -- |  (:<~>:)  -- ^ XOR
              deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- http://hackage.haskell.org/trac/ghc/ticket/4136
instance Read BinOp where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:<=>:), ":<=>:"),
                 -- ((:<~>:), ":<~>:"),
                 ((:=>:), ":=>:"),
                 -- ((:<=:), ":<=:"),
                 -- ((:~&:), ":~&:"),
                 -- ((:~|:), ":~|:"),
                 ((:&:), ":&:"),
                 ((:|:), ":|:")]

-- |Convert any instance of a propositional logic expression to any other.
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
      a = undefined -- convertA

instance Version BinOp

$(deriveSerialize ''BinOp)

$(deriveNewData [''BinOp])
