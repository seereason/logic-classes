{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |Classes and types representing the result of the normal form
-- conversion functions.
module Logic.Normal
    ( Predicate(..)
    , Literal(..)
    , fromFirstOrder
    , ClauseNormalFormula(..)
    , ImplicativeNormalForm(..)
    , makeINF
    , makeINF'
    , prettyLit
    ) where

import Control.Monad.Writer (MonadPlus)
import Data.Generics (Data, Typeable)
import Data.List (intersperse)
import Logic.FirstOrder (FirstOrderFormula, Term(..), convertTerm, Pretty(pretty), prettyTerm)
import qualified Logic.FirstOrder as Logic
import Logic.Logic (Negatable(..), Boolean(..))
import qualified Logic.Logic as Logic
import qualified Logic.Set as S
import Text.PrettyPrint (Doc, text, (<>), (<+>), empty, parens, hcat, nest)

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
      ) => Literal lit term v p f | lit -> term, lit -> v, lit -> p, lit -> f where
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

-- |A type to represent a formula in Implicative Normal Form.  Such a
-- formula has the form @a & b & c .=>. d | e | f@, where a thru f are
-- literals.  One more restriction that is not implied by the type is
-- that no literal can appear in both the pos set and the neg set.
data (Negatable lit, Ord lit) => ImplicativeNormalForm lit =
    INF {neg :: S.Set lit, pos :: S.Set lit}
    deriving (Eq, Ord, Data, Typeable)

-- |Synonym for INF.
makeINF :: (Negatable lit, Ord lit) => S.Set lit -> S.Set lit -> ImplicativeNormalForm lit
makeINF = INF

-- |A version of MakeINF that takes lists instead of sets, used for
-- implementing a more attractive show method.
makeINF' :: (Negatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeNormalForm lit
makeINF' n p = makeINF (S.fromList n) (S.fromList p)

instance (Ord formula, FirstOrderFormula formula term v p f, Show formula) => Show (ImplicativeNormalForm formula) where
    show x = "makeINF' (" ++ show (S.toList (neg x)) ++ ") (" ++ show (S.toList (pos x)) ++ ")"

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula term v p f lit term2 v2 p2 f2.
                  (Logic.FirstOrderFormula formula term v p f, Literal lit term2 v2 p2 f2) =>
                  (v -> v2) -> (p -> p2) -> (f -> f2) -> formula -> lit
fromFirstOrder cv cp cf formula =
    Logic.foldF (\ _ _ _ -> error "toLiteral q") c p formula
    where
      c :: Logic.Combine formula -> lit
      c ((Logic.:~:) f) =  (.~.) (fromFirstOrder cv cp cf f)
      c _ = error "fromFirstOrder"
      p :: Logic.Predicate p term -> lit
      p (Logic.Equal a b) = ct a .=. ct b
      p (Logic.NotEqual a b) = (.~.) (ct a .=. ct b)
      p (Logic.Apply pr ts) = pApp (cp pr) (map ct ts)
      p (Logic.Constant b) = error $ "fromFirstOrder " ++ show b
      ct = convertTerm cv cf

prettyLit :: forall lit term v p f. (Literal lit term v p f, Pretty p) =>
              Int -> lit -> Doc
prettyLit prec lit =
    foldN c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLit 5 x else prettyLit 5 x
      p (Equal t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "=" <+> prettyTerm t2)
      p (Apply pr ts) =
          pretty pr <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map prettyTerm ts)))
      parensIf False = id
      parensIf _ = parens . nest 1
