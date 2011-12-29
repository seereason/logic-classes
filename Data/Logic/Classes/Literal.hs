{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Classes.Literal
    ( Literal(..)
    , fromFirstOrder
    , prettyLit
    ) where

import Data.List (intersperse)
import Data.Logic.Classes.Atom (Atom(foldAtom, apply))
import Data.Logic.Classes.Combine (Combination(..))
import Data.Logic.Classes.Constants
import Data.Logic.Classes.FirstOrder
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term
import Text.PrettyPrint (Doc, (<>), text, empty, parens, hcat)

-- |Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class ( Negatable lit
      , Constants lit
      , Show lit
{-
      , Ord lit
      , Eq p
      , Ord p
      , Constants p
      , Term term v f
      , Data lit
-}
      ) => Literal lit atom v | lit -> atom v where
    -- equals :: term -> term -> lit
    -- pAppLiteral :: p -> [term] -> lit
    foldLiteral :: (lit -> r) -> (atom -> r) -> lit -> r
    zipLiterals :: (lit -> lit -> Maybe r)
                -> (atom -> atom -> Maybe r)
                -> lit -> lit -> Maybe r
    atomic :: atom -> lit

{-
-- |Helper type to implement the fold function for 'Literal'.
data PredicateLit p term
    = ApplyLit p [term]
    | EqualLit term term
-}

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula atom term v p f lit atom2 term2 v2 p2 f2.
                  (FirstOrderFormula formula atom v, Atom atom p term, Term term v f,
                   Literal lit atom2 v2, Atom atom2 p2 term2, Term term2 v2 f2) =>
                  (v -> v2) -> (p -> p2) -> (f -> f2) -> formula -> lit
fromFirstOrder cv cp cf formula =
    foldFirstOrder (\ _ _ _ -> error "toLiteral q") co tf at formula
    where
      co :: Combination formula -> lit
      co ((:~:) f) =  (.~.) (fromFirstOrder cv cp cf f)
      co _ = error "FirstOrder -> Literal"
      tf = fromBool
      at :: atom -> lit
      at = foldAtom (\ pr ts -> Data.Logic.Classes.Literal.atomic (apply (cp pr) (map ct ts))) fromBool
      ct = convertTerm cv cf

prettyLit :: forall lit atom term v p f. (Literal lit atom v, Atom atom p term, Term term v f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLit pv pp pf _prec lit =
    foldLiteral c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLit pv pp pf 5 x else prettyLit pv pp pf 5 x
      p = foldAtom (\ pr ts -> 
                        pp pr <> case ts of
                                   [] -> empty
                                   _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                   (\ x -> text $ if x then "true" else "false")
      -- parensIf False = id
      -- parensIf _ = parens . nest 1
