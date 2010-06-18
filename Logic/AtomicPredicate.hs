{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
module Logic.AtomicPredicate
    ( AtomicPredicate(..)
    ) where

import Data.Data (Data)
import qualified Data.Text as T
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
--import Logic.AtomicWord (AtomicWord(..))
import Logic.Basic (Belief(..), LinguisticHint(..), NounPhraseFragment(..), SubjectId(..), AssetId(..), AssertionId(..))

-- |Various types of primitive predicates.  A formula is created from
-- one of these using PredApp: let x = Users in PredApp x [Var (V
-- "x")].  This is a formula with one free variable, which we are
-- calling a Predicate.
data AtomicPredicate u pred w
    = Description LinguisticHint [NounPhraseFragment] -- ^ Is the term an element of the described set?
    | Reference SubjectId -- ^ Is the term a member of the subject set?
    | Somebody u -- ^ Is the term a particular user?
    | Users -- ^ Is the term a user?
    | Persons -- ^ Is the term a person?
    | Believers Belief -- ^ Is the term someone who accepts a Belief?
    | AssetReference AssetId -- ^ Is the term this exact asset?
    | Nickname T.Text -- ^ Does not affect membership
    | NumberOf pred -- ^ Is the term a number which matches the cardinality of a set.
    | AssertionRef AssertionId -- ^ Is the term 
    | Commentary T.Text -- ^ Does not affect membership
    | Atom w -- ^ The generic predicates used in Logic-TPTP
    | Singleton -- ^ I'm not sure this is a meaningful predicate in first order logic.
    deriving (Eq,Ord,Show,Read,Data,Typeable)

instance Version (AtomicPredicate u pred w)
$(deriveSerialize ''AtomicPredicate)
$(deriveNewData [''AtomicPredicate])
