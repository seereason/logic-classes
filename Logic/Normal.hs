{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |Classes and types representing the result of the normal form
-- conversion functions.
module Logic.Normal
    ( Predicate(..)
    , Literal(..)
    , fromFirstOrder
    , ClauseNormalFormula(..)
    , ImplicativeNormalFormula(..)
    ) where

import Control.Monad.Writer (MonadPlus)
import Data.Generics (Data)
import Logic.FirstOrder (Term(..))
import qualified Logic.FirstOrder as Logic
import Logic.Logic (Negatable(..), Boolean(..))
import qualified Logic.Logic as Logic
import qualified Logic.Set as S

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
      , Term term v f
      , Negatable lit
      , Data lit
      ) => Literal lit term v p f | lit -> term, term -> lit, lit -> v, lit -> p, lit -> f where
    (.=.) :: term -> term -> lit
    pApp :: p -> [term] -> lit
    foldN :: (lit -> r) -> (Predicate p term -> r) -> lit -> r
    zipN :: (lit -> lit -> Maybe r) -> (Predicate p term -> Predicate p term -> Maybe r) -> lit -> lit -> Maybe r

-- |A class to represent formulas in CNF, which is the conjunction of
-- a set of disjuncted literals each which may or may not be negated.
class (Negatable lit, Eq lit, Ord lit) => ClauseNormalFormula cnf lit | cnf -> lit where
    clauses :: cnf -> S.Set (S.Set lit)
    makeCNF :: S.Set (S.Set lit) -> cnf
    satisfiable :: MonadPlus m => cnf -> m Bool

-- |A class to represent types that express a formula in Implicative
-- Normal Form.  Such a formula has the form @a & b & c .=>. d | e |
-- f@, where a thru f are literals.  One more restriction that is not
-- implied by the type is that no literal can appear in both the pos
-- set and the neg set.  Minimum implementation: pos, neg, toINF
class (Negatable lit, Eq inf, Ord inf, Ord lit) => ImplicativeNormalFormula inf lit | inf -> lit where
    neg :: inf -> S.Set lit
                         -- ^ Return the literals that are negated
                         -- and disjuncted on the left side of the
                         -- implies.  @neg@ and @pos@ are sets in
                         -- some sense, but we don't (yet) have
                         -- suitable Eq and Ord instances that
                         -- understand renaming.
    pos :: inf -> S.Set lit
                         -- ^ Return the literals that are
                         -- conjuncted on the right side of the
                         -- implies.
    makeINF :: S.Set lit -> S.Set lit -> inf

-- |We can implement a Literal instance using methods from
-- FirstOrderFormula.
instance Logic.FirstOrderFormula formula term v p f => Literal formula term v p f where
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

-- |Convert any first order logic formula to a normal logic formula,
-- |provided it doesn't contain any unsupported constructs, such as
-- |quantifiers, binary operators, boolean constants.
fromFirstOrder :: forall formula term v p f lit. (Logic.FirstOrderFormula formula term v p f, Literal lit term v p f) => formula -> lit
fromFirstOrder formula =
    Logic.foldF (\ _ _ _ -> error "toLiteral") c p formula
    where
      c :: Logic.Combine formula -> lit
      c ((Logic.:~:) f) =  (.~.) (fromFirstOrder f)
      c _ = error "comvertToNormal"
      p :: Logic.Predicate p term -> lit
      p (Logic.Equal a b) = a .=. b
      p (Logic.Apply pr ts) = pApp pr ts
      p _ = error "toLiteral"
