{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-incomplete-patterns #-}
-- |
-- Module      : Data.Boolean
-- Copyright   : Sebastian Fischer
-- License     : BSD3
--
-- Maintainer  : Sebastian Fischer (sebf@informatik.uni-kiel.de)
-- Stability   : experimental
-- Portability : portable
--
-- This library provides a representation of boolean formulas that is
-- used by the solver in "Data.Boolean.SatSolver".
--
-- We also define a function to simplify formulas, a type for
-- conjunctive normalforms, and a function that creates them from
-- boolean formulas.
--
module Data.Boolean (

  Boolean(..),

  Literal(..), literalVar, invLiteral, isPositiveLiteral,

  CNF, Clause, booleanToCNF

  ) where

import Control.Monad ( guard, liftM )
import Data.Generics (Data, Typeable)
import qualified Data.IntMap as IM
import Data.Logic.ATP.Formulas (IsAtom, IsFormula(..))
import Data.Logic.ATP.Lit (IsLiteral(..))
import Data.Logic.ATP.Prop (IsPropositional(..), JustPropositional)
import Data.Logic.ATP.Pretty (HasFixity(..), Pretty(pPrint), text)
import Data.Maybe ( mapMaybe )

-- | Boolean formulas are represented as values of type @Boolean@.
--
data Boolean
  -- | Variables are labeled with an @Int@,
  = Var Int
  -- | @Yes@ represents /true/,
  | Yes
  -- | @No@ represents /false/,
  | No
  -- | @Not@ constructs negated formulas,
  | Not Boolean
  -- | and finally we provide conjunction
  | Boolean :&&: Boolean
  -- | and disjunction of boolean formulas.
  | Boolean :||: Boolean
 deriving Show

-- | Literals are variables that occur either positively or negatively.
--
data Literal = Pos Int | Neg Int deriving (Eq, Show)

instance Ord Literal where
    compare (Neg _) (Pos _) = LT
    compare (Pos _) (Neg _) = GT
    compare (Pos m) (Pos n) = compare m n
    compare (Neg m) (Neg n) = compare m n

deriving instance Data Literal
deriving instance Typeable Literal

-- | This function returns the name of the variable in a literal.
--
literalVar :: Literal -> Int
literalVar (Pos n) = n
literalVar (Neg n) = n

-- | This function negates a literal.
--
invLiteral :: Literal -> Literal
invLiteral (Pos n) = Neg n
invLiteral (Neg n) = Pos n

-- | This predicate checks whether the given literal is positive.
--
isPositiveLiteral :: Literal -> Bool
isPositiveLiteral (Pos _) = True
isPositiveLiteral _       = False

-- | Conjunctive normalforms are lists of lists of literals.
--
type CNF     = [Clause]
type Clause  = [Literal]

instance JustPropositional CNF

instance HasFixity Int

instance IsAtom Int

instance IsFormula CNF where
    type AtomOf CNF = Int
    atomic = error "FIXME: IsFormula CNF MyAtom"
    overatoms = error "FIXME: IsFormula CNF MyAtom"
    onatoms = error "FIXME: IsFormula CNF MyAtom"
    asBool = error "FIXME: HasBoolean CNF"
    true = error "FIXME: HasBoolean CNF"
    false = error "FIXME: HasBoolean CNF"
instance Pretty Literal where
    pPrint = text . show
instance IsPropositional CNF where
    foldPropositional' = error "FIXME: IsPropositional CNF MyAtom"
    foldCombination = error "FIXME: IsCombinable CNF"
    _ .|. _ = error "FIXME: IsCombinable CNF"
    _ .&. _ = error "FIXME: IsCombinable CNF"
    _ .=>. _ = error "FIXME: IsCombinable CNF"
    _ .<=>. _ = error "FIXME: IsCombinable CNF"
instance HasFixity CNF where
    precedence _ = error "FIXME: HasFixity CNF"
    associativity _ = error "FIXME: HasFixity CNF"
instance IsLiteral CNF where
    foldLiteral' = error "FIXME: IsLiteral CNF MyAtom"
    naiveNegate = error "FIXME: IsNegatable CNF"
    foldNegation = error "FIXME: IsNegatable CNF"

-- |
-- We convert boolean formulas to conjunctive normal form by pushing
-- negations down to variables and repeatedly applying the
-- distributive laws.
--
booleanToCNF :: Boolean -> CNF
booleanToCNF
  = mapMaybe (simpleClause . map literal . disjunction)
  . conjunction
  . asLongAsPossible distribute
  . asLongAsPossible pushNots
  . asLongAsPossible elim
 where
  elim (Not Yes)      = Just No
  elim (Not No)       = Just Yes
  elim (No  :&&: _)   = Just No
  elim (Yes :&&: x)   = Just x
  elim (_   :&&: No)  = Just No
  elim (x   :&&: Yes) = Just x
  elim (Yes :||: _)   = Just Yes
  elim (No  :||: x)   = Just x
  elim (_   :||: Yes) = Just Yes
  elim (x   :||: No)  = Just x
  elim _              = Nothing

  pushNots (Not (Not x))  = Just x
  pushNots (Not (x:&&:y)) = Just (Not x :||: Not y)
  pushNots (Not (x:||:y)) = Just (Not x :&&: Not y)
  pushNots _              = Nothing

  distribute (x:||:(y:&&:z)) = Just ((x:||:y):&&:(x:||:z))
  distribute ((x:&&:y):||:z) = Just ((x:||:z):&&:(y:||:z))
  distribute _               = Nothing

  literal (Var x)       = Pos x
  literal (Not (Var x)) = Neg x


-- private helper functions

-- remove duplicate literals from clauses and drop clauses that
-- contain one literal both positively and negatively.
--
simpleClause :: Clause -> Maybe Clause
simpleClause = liftM (map lit . IM.toList) . foldl add (Just IM.empty)
 where
  lit (x,True)  = Pos x
  lit (x,False) = Neg x

  add mm l = do
    m <- mm
    let x = literalVar l; kind = isPositiveLiteral l
    maybe (Just (IM.insert x kind m))
          (\b -> guard (b==kind) >> Just m)
          (IM.lookup x m)

conjunction :: Boolean -> [Boolean]
conjunction b = flat b []
 where flat Yes      = id
       flat (x:&&:y) = flat x . flat y
       flat x        = (x:)

disjunction :: Boolean -> [Boolean]
disjunction b = flat b []
 where flat No       = id
       flat (x:||:y) = flat x . flat y
       flat x        = (x:)

asLongAsPossible :: (Boolean -> Maybe Boolean) -> Boolean -> Boolean
asLongAsPossible f = everywhere g
 where g x = maybe x (everywhere g) (f x)

everywhere :: (Boolean -> Boolean) -> Boolean -> Boolean
everywhere f = f . atChildren (everywhere f)

atChildren :: (Boolean -> Boolean) -> Boolean -> Boolean
atChildren f (Not x)  = Not (f x)
atChildren f (x:&&:y) = f x :&&: f y
atChildren f (x:||:y) = f x :||: f y
atChildren _ x        = x

