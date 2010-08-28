{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |A simplified formula type which is suitable for use as the
-- parameter to the Literal class after converting a first order logic
-- formula to normal form.
module Logic.Normal
    ( Predicate(..)
    , NormalLogic(..)
    ) where

import Data.Generics (Data)
import Logic.Clause (Literal(..))
import Logic.FirstOrder (Term(..))
import qualified Logic.FirstOrder as Logic
import Logic.Logic (Boolean(..))
import qualified Logic.Logic as Logic

-- |Caution - There are similar declarations with similar names in the
-- FirstOrder module, these are simplified versions suitable for
-- formulas that come out of the normal form functions.
data Predicate p term
    = Apply p [term]
    | Equal term term

class ( Ord lit
      , Eq p
      , Ord p
      , Boolean p
      , Data p
      , Term term v f
      ) => NormalLogic lit term v p f | lit -> term, term -> lit, lit -> v, term -> v, lit -> p, term -> f, lit -> f where
    (.~.) :: lit -> lit
    (.=.) :: term -> term -> lit
    pApp :: p -> [term] -> lit
    foldN :: (lit -> r) -> (Predicate p term -> r) -> lit -> r
    zipN :: (lit -> lit -> Maybe r) -> (Predicate p term -> Predicate p term -> Maybe r) -> lit -> lit -> Maybe r

instance (Ord lit, NormalLogic lit term v p f) => Literal lit where
    inverted l = foldN (not . inverted) (\ _ -> False) l
    invert f = foldN unvert (\ _ -> (.~.) f) f
        where unvert = foldN invert (\ _ -> f)

instance (Logic.FirstOrderLogic formula term v p f, Ord formula, Ord p, Data p) => NormalLogic formula term v p f where
    (.~.) = (Logic..~.)
    (.=.) = (Logic..=.)
    pApp = Logic.pApp
    foldN c p l =
        Logic.foldF (\ _ _ _ -> error "foldN") c' p' l
        where
          c' ((Logic.:~:) x) = c x
          c' _ = error "foldN"
          p' (Logic.Equal a b) = p (Equal a b)
          p' (Logic.Apply pr ts) = p (Apply pr ts)
          p' _ = error "foldN"
    zipN c p l1 l2 =
        Logic.zipF (\ _ _ _ _ _ _ -> error "zipN") c' p' l1 l2
        where
          c' ((Logic.:~:) x) ((Logic.:~:) y) = c x y
          c'  _ _ = error "zipN"
          p' (Logic.Equal a1 b1) (Logic.Equal a2 b2) = p (Equal a1 b1) (Equal a2 b2)
          p' (Logic.Apply p1 ts1) (Logic.Apply p2 ts2) = p (Apply p1 ts1) (Apply p2 ts2)
          p' _ _ = error "zipN"
