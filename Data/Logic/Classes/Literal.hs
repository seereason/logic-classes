{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Classes.Literal
    ( Literal(..)
    , PredicateLit(..)
    , fromFirstOrder
    , prettyLit
    ) where

import Data.Generics (Data)
import Data.List (intersperse)
import Data.Logic.Classes.Combine (Combination(..))
import Data.Logic.Classes.Constants
import Data.Logic.Classes.FirstOrder
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

-- |Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class ( Ord lit
      , Eq p
      , Ord p
      , Constants p
      , Term term v f
      , Negatable lit
      , Data lit
      , Show lit
      ) => Literal lit term v p f | lit -> term, lit -> v, lit -> p, lit -> f where
    equals :: term -> term -> lit
    pAppLiteral :: p -> [term] -> lit
    foldLiteral :: (lit -> r) -> (PredicateLit p term -> r) -> lit -> r
    zipLiterals :: (lit -> lit -> Maybe r) -> (PredicateLit p term -> PredicateLit p term -> Maybe r) -> lit -> lit -> Maybe r
    atomic :: PredicateLit p term -> lit

-- |Helper type to implement the fold function for 'Literal'.
data PredicateLit p term
    = ApplyLit p [term]
    | EqualLit term term

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula term v p f lit term2 v2 p2 f2.
                  (FirstOrderFormula formula term v p f, Literal lit term2 v2 p2 f2) =>
                  (v -> v2) -> (p -> p2) -> (f -> f2) -> formula -> lit
fromFirstOrder cv cp cf formula =
    foldFirstOrder (\ _ _ _ -> error "toLiteral q") c p formula
    where
      c :: Combination formula -> lit
      c ((:~:) f) =  (.~.) (fromFirstOrder cv cp cf f)
      c _ = error "fromFirstOrder"
      p :: Predicate p term -> lit
      p (Equal a b) = ct a `equals` ct b
      p (NotEqual a b) = (.~.) (ct a `equals` ct b)
      p (Apply pr ts) = pAppLiteral (cp pr) (map ct ts)
      p (Constant b) = error $ "fromFirstOrder " ++ show b
      ct = convertTerm cv cf

prettyLit :: forall lit term v p f. (Literal lit term v p f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLit pv pp pf prec lit =
    foldLiteral c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLit pv pp pf 5 x else prettyLit pv pp pf 5 x
      p (ApplyLit pr ts) =
          pp pr <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts)))
      p (EqualLit t1 t2) = parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2)
      parensIf False = id
      parensIf _ = parens . nest 1
