module Logic.Set
    ( ss
    , any
    , all
    , and
    , or
    , distrib
    , flatten
    , toSS
    , fromSS
    , mapM
    , ssMapM
    , cartesianProduct
    , module Data.Set
    ) where

import qualified Control.Monad as M
import qualified Data.List as L
import Data.Set
import Prelude hiding (any, all, null, filter, map, and, or, mapM)

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

mapM :: (Monad m, Ord b) => (a -> m b) -> Set a -> m (Set b)
mapM f s = M.mapM f (toList s) >>= return . fromList

ssMapM :: (Monad m, Ord a, Ord b) => (a -> m b) -> Set (Set a) -> m (Set (Set b))
ssMapM f s = M.mapM (M.mapM f) (fromSS s) >>= return . toSS

toSS :: Ord a => [[a]] -> Set (Set a)
toSS = fromList . L.map fromList

fromSS :: Ord a => Set (Set a) -> [[a]]
fromSS = L.map toList . toList

cartesianProduct :: (Ord a, Ord b) => Set a -> Set b -> Set (a, b)
cartesianProduct xs ys = flatten $ Data.Set.map (\ x -> Data.Set.map (\ y -> (x, y)) ys) xs
