{-# OPTIONS -Wwarn #-}
module Data.Logic
    ( -- * Boolean Logic
      Negatable(..)
    , Constants(..)
    , Combinable(..)
    -- * Propositional Logic
    , PropositionalFormula(..)
    , Combine(..)
    , BinOp(..)
    -- * FirstOrderLogic
    , Variable(variant, prefix, prettyVariable) -- omit fromString, get it from Variable module if necessary
    , variants
    , Arity(arity)
    , Pred(..)
    , pApp
    , Predicate(..)
    , Skolem(..)
    , Term(..)
    , FirstOrderFormula(..)
    -- * Normal Forms
    , Literal(..)
    , ClauseNormalFormula(..)
    , ImplicativeForm(..)
    -- * Knowledge Base and Theorem Proving
    , Proof(proofResult)
    , ProofResult(Proved, Invalid, Disproved)
    , tellKB
    , runProverT'
    , prettyProof
    ) where

import Data.Logic.Classes.Arity
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants
import Data.Logic.Classes.ClauseNormalForm
import Data.Logic.Classes.FirstOrder
import Data.Logic.Classes.Literal
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Propositional
import Data.Logic.Classes.Skolem
import Data.Logic.Classes.Term
import Data.Logic.Classes.Variable
import Data.Logic.KnowledgeBase
import Data.Logic.Normal.Implicative
import Data.Logic.Types.FirstOrder ()
import Data.Logic.Types.FirstOrderPublic ()
