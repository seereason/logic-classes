{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Classes.Literal
    ( Literal(..)
    , zipLiterals
    , fromFirstOrder
    , fromLiteral
    , prettyLit
    ) where

import Data.List (intersperse)
import Data.Logic.Classes.Atom (Atom(foldAtom))
import Data.Logic.Classes.Combine (Combination(..))
import Data.Logic.Classes.Constants
import qualified Data.Logic.Classes.FirstOrder as FOF
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term
import Text.PrettyPrint (Doc, (<>), text, empty, parens, hcat)

-- |Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (Negatable lit, Constants lit) => Literal lit atom v | lit -> atom v where
    foldLiteral :: (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r
    atomic :: atom -> lit

zipLiterals :: Literal lit atom v =>
               (lit -> lit -> Maybe r)
            -> (Bool -> Bool -> Maybe r)
            -> (atom -> atom -> Maybe r)
            -> lit -> lit -> Maybe r
zipLiterals neg tf at fm1 fm2 =
    foldLiteral neg' tf' at' fm1
    where
      neg' p1 = foldLiteral (neg p1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldLiteral (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' a1 = foldLiteral (\ _ -> Nothing) (\ _ -> Nothing) (at a1) fm2

{- This makes bad things happen.
-- | We can use an fof type as a lit, but it must not use some constructs.
instance FirstOrderFormula fof atom v => Literal fof atom v where
    foldLiteral neg tf at fm = foldFirstOrder qu co tf at fm
        where qu = error "instance Literal FirstOrderFormula"
              co ((:~:) x) = neg x
              co _ = error "instance Literal FirstOrderFormula"
    atomic = Data.Logic.Classes.FirstOrder.atomic
-}

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula atom v lit atom2 v2.
                  (FOF.FirstOrderFormula formula atom v, Literal lit atom2 v2) =>
                  (atom -> atom2) -> (v -> v2) -> formula -> lit
fromFirstOrder ca cv formula =
    FOF.foldFirstOrder (\ _ _ _ -> error "FirstOrder -> Literal") co fromBool (atomic . ca) formula
    where
      co :: Combination formula -> lit
      co ((:~:) f) =  (.~.) (fromFirstOrder ca cv f)
      co _ = error "FirstOrder -> Literal"

fromLiteral :: forall lit atom v fof atom2 v2. (Literal lit atom v, FOF.FirstOrderFormula fof atom2 v2) =>
               (atom -> atom2) -> lit -> fof
fromLiteral ca lit = foldLiteral (\ p -> (.~.) (fromLiteral ca p)) fromBool (FOF.atomic . ca) lit

prettyLit :: forall lit atom term v p f. (Literal lit atom v, Atom atom p term, Term term v f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLit pv pp pf _prec lit =
    foldLiteral neg tf at lit
    where
      neg :: lit -> Doc
      neg x = if negated x then text {-"¬"-} "~" <> prettyLit pv pp pf 5 x else prettyLit pv pp pf 5 x
      tf = text . ifElse "true" "false"
      at = foldAtom (\ pr ts -> 
                        pp pr <> case ts of
                                   [] -> empty
                                   _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                   (\ x -> text $ if x then "true" else "false")
      -- parensIf False = id
      -- parensIf _ = parens . nest 1
