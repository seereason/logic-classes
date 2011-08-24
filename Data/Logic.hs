{-# OPTIONS -Wwarn #-}
module Data.Logic
    ( Arity(arity)
    , Variable(one, next)
    , Negatable(..)
    , Pred(..)
    , Logic(..)
    , Term(..)
    , FirstOrderFormula(..)
    , Data.Logic.Predicate.pApp
    , Data.Logic.Predicate.Predicate(Apply)
    , ImplicativeNormalForm
    , Literal
    , tellKB
    , runProverT'
    , ProofResult(Proved, Invalid, Disproved)
    , Proof
    ) where

import Data.Logic.FirstOrder
import qualified Data.Logic.Instances.Native as N
import qualified Data.Logic.Instances.Public as P
import Data.Logic.KnowledgeBase
import Data.Logic.Monad
import Data.Logic.NormalForm
import Data.Logic.Normal as N
import Data.Logic.Logic
import Data.Logic.Predicate
import Data.Logic.Pretty
import Data.Logic.Propositional
import Data.Logic.Resolution
