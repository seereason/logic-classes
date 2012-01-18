{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Classes.Literal
    ( Literal(..)
    , zipLiterals
    , fromFirstOrder
    , fromLiteral
    , toPropositional
    , prettyLit
    ) where

import Control.Applicative.Error (Failing(..))
import Data.Logic.Classes.Combine (Combination(..))
import Data.Logic.Classes.Constants
import qualified Data.Logic.Classes.FirstOrder as FOF
import Data.Logic.Classes.Pretty (HasFixity(..), Fixity(..), FixityDirection(..))
import qualified Data.Logic.Classes.Propositional as P
import Data.Logic.Classes.Negate
import Text.PrettyPrint (Doc, (<>), text, parens, nest)

-- |Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (Negatable lit, Constants lit, HasFixity atom) => Literal lit atom v | lit -> atom v where
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
                  (atom -> atom2) -> (v -> v2) -> formula -> Failing lit
fromFirstOrder ca cv formula =
    FOF.foldFirstOrder (\ _ _ _ -> Failure ["fromFirstOrder"]) co (Success . fromBool) (Success . atomic . ca) formula
    where
      co :: Combination formula -> Failing lit
      co ((:~:) f) =  fromFirstOrder ca cv f >>= return . (.~.)
      co _ = Failure ["fromFirstOrder"]

fromLiteral :: forall lit atom v fof atom2 v2. (Literal lit atom v, FOF.FirstOrderFormula fof atom2 v2) =>
               (atom -> atom2) -> lit -> fof
fromLiteral ca lit = foldLiteral (\ p -> (.~.) (fromLiteral ca p)) fromBool (FOF.atomic . ca) lit

toPropositional :: forall lit atom v pf atom2. (Literal lit atom v, P.PropositionalFormula pf atom2) =>
                   (atom -> atom2) -> lit -> pf
toPropositional ca lit = foldLiteral (\ p -> (.~.) (toPropositional ca p)) fromBool (P.atomic . ca) lit

{-
prettyLit :: forall lit atom term v p f. (Literal lit atom v, Apply atom p term, Term term v f) =>
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
      at = foldApply (\ pr ts -> 
                        pp pr <> case ts of
                                   [] -> empty
                                   _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                   (\ x -> text $ if x then "true" else "false")
      -- parensIf False = id
      -- parensIf _ = parens . nest 1
-}

prettyLit :: forall lit atom v. (Literal lit atom v) =>
              (Int -> atom -> Doc)
           -> (v -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLit pa pv pprec lit =
    parensIf (pprec > prec) $ foldLiteral co tf at lit
    where
      co :: lit -> Doc
      co x = if negated x then text {-"¬"-} "~" <> prettyLit pa pv 5 x else prettyLit pa pv 5 x
      tf x = text (if x then "true" else "false")
      at = pa 6
      parensIf False = id
      parensIf _ = parens . nest 1
      Fixity prec _ = fixityLiteral lit

fixityLiteral :: (Literal formula atom v) => formula -> Fixity
fixityLiteral formula =
    foldLiteral neg tf at formula
    where
      neg _ = Fixity 5 InfixN
      tf _ = Fixity 10 InfixN
      at = fixity
