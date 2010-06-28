{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# OPTIONS -fno-warn-orphans #-}
module Logic.Instances.PropLogic where

import PropLogic
import Logic.Logic
import Logic.Propositional

instance Logic (PropForm a) where
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]
    (.~.) x   = N x

instance (Logic (PropForm a), Show a) => PropositionalLogic (PropForm a) a where
    atomic = A
    foldF0 n b a formula =
        case formula of
          -- EJ [x,y,z,...] -> CJ [EJ [x,y], EJ[y,z], ...]
          EJ xs -> case pairs xs of
                     [] -> foldF0 n b a (head xs)
                     [(x, y)] -> b x (:<=>:) y
                     ps -> foldF0 n b a (CJ (map (\ (x, y) -> EJ [x, y]) ps))
          SJ xs -> case pairs xs of
                     [] -> foldF0 n b a (head xs)
                     [(x, y)] -> b x (:=>:) y
                     ps -> foldF0 n b a (CJ (map (\ (x, y) -> SJ [x, y]) ps))
          DJ [] -> error "Empty disjunct"
          DJ [x] -> foldF0 n b a x
          DJ (x0:xs) -> foldF0 n b a (foldl (\ f x -> DJ [f, x]) x0 xs)
          CJ [] -> error "Empty conjunct"
          CJ [x] -> foldF0 n b a x
          CJ (x0:xs) -> foldF0 n b a (foldl (\ f x -> CJ [f, x]) x0 xs)
          N x -> n x
          -- Not sure what to do about these - so far not an issue.
          T -> error "foldF0 method of PropForm: T"
          F -> error "foldF0 method of PropForm: F"
          A x -> a x

pairs :: [a] -> [(a, a)]
pairs (x:y:zs) = (x,y) : pairs (y:zs)
pairs _ = []

flatten :: PropForm a -> PropForm a
flatten (CJ xs) =
    CJ (concatMap f (map flatten xs))
    where
      f (CJ ys) = ys
      f x = [x]
flatten (DJ xs) =
    DJ (concatMap f (map flatten xs))
    where
      f (DJ ys) = ys
      f x = [x]
flatten (EJ xs) = EJ (map flatten xs)
flatten (SJ xs) = SJ (map flatten xs)
flatten (N x) = N (flatten x)
flatten x = x
