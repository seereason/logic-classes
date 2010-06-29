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
    , showForm0
    , convertProp
    ) where

import Logic.Logic

-- |A type class for propositional logic.  If the type we are writing
-- an instance for is a zero-order (aka propositional) logic type
-- there will generally by a type or a type parameter corresponding to
-- atom.  For first order or predicate logic types, it is generally
-- easiest to just use the formula type itself as the atom type, and
-- raise errors in the implementation if a non-atomic formula somehow
-- appears where an atomic formula is expected (i.e. as an argument to
-- atomic or to the third argument of foldF0.)
class Logic formula => PropositionalLogic formula atom | formula -> atom where
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

-- | Show a formula in a format that can be evaluated 
showForm0 :: (PropositionalLogic formula atom) => (atom -> String) -> formula -> String
showForm0 showAtom formula =
    foldF0 n b a formula
    where
      n f = "(.~.) " ++ parenForm f
      b f1 op f2 = parenForm f1 ++ " " ++ showFormOp op ++ " " ++ parenForm f2
      a = showAtom
      parenForm x = "(" ++ showForm0 showAtom x ++ ")"
      showFormOp (:<=>:) = ".<=>."
      showFormOp (:=>:) = ".=>."
      showFormOp (:&:) = ".&."
      showFormOp (:|:) = ".|."

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
