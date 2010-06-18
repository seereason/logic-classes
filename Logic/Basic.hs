{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             StandaloneDeriving, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Logic.Basic
    ( AssertionId(..)
    , AssertionState(..)
    , SubjectId(..)
    , AssetId(..)
    , NounPhraseFragment(..)
    , LinguisticHint(..)
    , ap, np, asp
    , Document(..)
    , title'
    , SubDocument(..)
    , TextRange(..)
    , getSubDocument
    , Asset(..)
    , Assets
    , Belief(..)
    ) where

import Data.Data (Data(..))
import qualified Data.Generics.SYB.WithClass.Basics as New
import qualified Data.Graph.Inductive as Graph
import qualified Data.Text as T
import Data.Typeable (Typeable, Typeable1, Typeable2)
import Happstack.Data (Default(..), DefaultD, deriveNewData, deriveNewDataNoDefault, Serialize(..))
import Happstack.Data.IxSet (Indexable(..), inferIxSet, noCalcs)
import Happstack.Data.Serialize (contain, safeGet, safePut)
import Happstack.State (Version, deriveSerialize)

-- |Each value of type Subject represents a set.  The elements of the
-- set are determined by the propositions in which the subject appears
-- via the Reference predicate.  Thus, by itself a Subject is just a
-- meaningless identifier which can be referred to in propositions.
-- It refers to an implied predicate which consists of the context
-- formed by the propositions in which it appears.  Users can agree or
-- disagree with each of these propositions (by adding assertions
-- containing Believer predicates about themselves.)
data SubjectId = SubjectId {unSubjectId :: Integer} deriving (Read, Show, Eq, Ord, Data, Typeable)

instance Enum SubjectId where
    toEnum = SubjectId . toInteger
    fromEnum (SubjectId n) = fromInteger n

$(deriveNewDataNoDefault [''SubjectId])

instance Default SubjectId where
    defaultValue = SubjectId 1

-- |A reference to an assertion by number.
newtype AssertionId = AssertionId {unAssertionId :: Integer}
    deriving (Eq, Ord, Read, Show, Data, Typeable)

instance Enum AssertionId where
    toEnum = AssertionId . toInteger
    fromEnum = fromInteger . unAssertionId

$(deriveNewDataNoDefault [''AssertionId])

instance Default AssertionId where
    defaultValue = AssertionId 1

deriving instance Typeable2 Graph.Gr

instance (Serialize a, Typeable a, Serialize b, Typeable b) => Serialize (Graph.Gr a b) where
    putCopy inp = contain (safePut (Graph.labNodes inp) >> safePut (Graph.labEdges inp))
    getCopy = contain (safeGet >>= \ nodes -> safeGet >>= \ edges -> return (Graph.mkGraph nodes edges))

instance Version (Graph.Gr a b)

instance (New.Data DefaultD a, New.Data DefaultD b) => New.Data DefaultD (Graph.Gr a b) where
    toConstr = error "toConstr Data.Graph.Inductive.Gr"

instance (New.Data DefaultD a, New.Data DefaultD b) => Default (Graph.Gr a b) where
    defaultValue = Graph.empty

deriving instance Typeable1 Graph.NodeMap

instance Version (Graph.NodeMap a)

instance (New.Data DefaultD a, Ord a) => New.Data DefaultD (Graph.NodeMap a) where
    toConstr = error "toConstr Data.Graph.Inductive.NodeMap"

instance (New.Data DefaultD a, Ord a) => Default (Graph.NodeMap a) where
    defaultValue = Graph.new

-- |A reference to an assertion by number.
newtype AssetId = AssetId {unAssetId :: Integer}
    deriving (Eq, Ord, Read, Show, Data, Typeable)

instance Enum AssetId where
    toEnum = AssetId . toInteger
    fromEnum = fromInteger . unAssetId

$(deriveNewDataNoDefault [''AssetId])

instance Default AssetId where
    defaultValue = AssetId 1

-- |The life cycle of an assertion.
data AssertionState
    = Proposed   -- ^ Under construction, an editing form will be displayed
    | Private    -- ^ Complete, but still visible only to owner, can return to Proposed state
    | Published  -- ^ Public, can not be altered
    deriving (Read, Show, Eq, Ord, Data, Typeable)

-- |Hints used to combine descriptions, they should be presented in
-- the order given here.
data LinguisticHint
    = AdjectivePhrase       -- ^ e.g. "very wealthy."
    | NounPhrase            -- ^ e.g. "the wealthy."
    | AdjectiveSuffixPhrase -- ^ e.g. "of great wealth."
    deriving (Read, Show, Eq, Ord, Data, Typeable)

np :: LinguisticHint
np = NounPhrase
ap :: LinguisticHint
ap = AdjectivePhrase
asp :: LinguisticHint
asp = AdjectiveSuffixPhrase

-- | A free form text description of a set.
data NounPhraseFragment =
    T T.Text | S SubjectId | D SubDocument | Number Double | Percentage Double
    deriving (Read, Show, Eq, Ord, Data, Typeable)

-- |A data structure representing a text document.  The Document
-- predicate is used to represent the singleton set containing a
-- document.  The authors field refers to a Subject describing the set
-- of authors of the document.
data Document
    = Text {authors :: SubjectId, title :: T.Text, text :: T.Text}
    | Brief {text :: T.Text}
    deriving (Read, Show, Eq, Ord, Data, Typeable)

title' :: Document -> T.Text
title' x@(Text {}) = title x
title' x@(Brief {}) = text x

data SubDocument
    = TextRanges {textRanges :: [TextRange], documentId :: AssetId}
    | Quotation {quotation :: T.Text, documentId :: AssetId}
    deriving (Read, Show, Eq, Ord, Data, Typeable)

data TextRange
    = TextRange {startPos :: Int, endPost :: Int}
    deriving (Read, Show, Eq, Ord, Data, Typeable)

-- |Assuming the second argument is the Document referred to by the
-- subject number in the SubDocument argument, return a Document
-- containing the referred to text.
getSubDocument :: SubDocument -> Document -> Maybe Document
getSubDocument (TextRanges {textRanges = ranges}) doc =
    case doc of
      Text {} ->
          Just (doc { title = T.append (T.pack "Excerpt of ") (title doc)
                    , text = T.intercalate (T.pack " ") (map get ranges) })
      Brief {} ->
          Just (doc {text = T.intercalate (T.pack " ") (map get ranges)})
    where
      get :: TextRange -> T.Text
      get (TextRange s e) = T.take (e - s + 1) (T.drop s (text doc))
getSubDocument (Quotation t _) d =
    Just (d {text = t})

-- |A belief is the association of an assertion with a truth value
-- indicating whether the assertion is accepted, rejected, or that one
-- has no opinion.  The Believers predicate above is used to construct
-- a set of people who accept or reject an assertion.  The user is
-- considered to have this belief about the assertion starting from
-- the time the belief is created until the creation of a new belief about
-- the same assertion.  This is why the truth value is a maybe, so that
-- a user who accepted or rejected an assertion to later have no opinion.
data Belief = Belief AssertionId (Maybe Bool) deriving (Read, Show, Eq, Ord, Data, Typeable)

data Asset
    = Document {assetId :: AssetId, document :: Document}
    deriving (Read, Show, Eq, Ord, Data, Typeable)

$(inferIxSet "Assets" ''Asset 'noCalcs [''AssetId, ''Document])

instance Version SubjectId
instance Version AssertionId
instance Version AssertionState
instance Version AssetId
instance Version Asset
instance Version LinguisticHint
instance Version Belief
instance Version NounPhraseFragment
instance Version Document
instance Version SubDocument
instance Version TextRange
$(deriveSerialize ''AssertionId)
$(deriveSerialize ''AssertionState)
$(deriveSerialize ''SubjectId)
$(deriveSerialize ''AssetId)
$(deriveSerialize ''Asset)
$(deriveSerialize ''LinguisticHint)
$(deriveSerialize ''Belief)
$(deriveSerialize ''NounPhraseFragment)
$(deriveSerialize ''Document)
$(deriveSerialize ''SubDocument)
$(deriveSerialize ''TextRange)
$(deriveNewData [''AssertionState, ''LinguisticHint, ''Belief, ''NounPhraseFragment,
                 ''Document, ''SubDocument, ''TextRange, ''Asset])
