module Logic.Set
    ( ss
    , any
    , all
    , and
    , or
    , distrib
    , flatten
    , module Data.Set
    ) where

import Data.Set
import Prelude hiding (any, all, null, filter, map, and, or)

any :: Ord a => (a -> Bool) -> Set a -> Bool
any f s = not . null . filter id . map f $ s

all :: Ord a => (a -> Bool) -> Set a -> Bool
all f s = not . null . filter not . map f $ s

ss :: Ord a => a -> Set (Set a)
ss = singleton . singleton

distrib :: Ord a => Set (Set a) -> Set (Set a) -> Set (Set a)
distrib lss rss = flatten $ map (\ rs -> (map (\ ls -> union rs ls) lss)) rss

flatten :: Ord a => Set (Set a) -> Set a
flatten = unions . toList

or :: Set Bool -> Bool
or = any id

and :: Set Bool -> Bool
and = all id
