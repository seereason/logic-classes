{-# LANGUAGE FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Classes.Literal
    ( IsLiteral(..)
    , zipLiterals
    , toPropositional
    , prettyLit
    , foldAtomsLiteral
    ) where

import Data.Logic.Classes.Constants
import Data.Logic.Classes.Formula (IsFormula(atomic))
import Data.Logic.Classes.Pretty (HasFixity(..), Fixity(..), FixityDirection(..))
import qualified Data.Logic.Classes.Propositional as P
import Data.Logic.Classes.Negate
import Text.PrettyPrint (Doc, (<>), text, parens, nest)

-- |Literals are the building blocks of the clause and implicative normal
-- |forms.  They support negation and must include True and False elements.
class (IsNegatable lit, HasBoolean lit, HasFixity atom, IsFormula lit atom, Ord lit) => IsLiteral lit atom | lit -> atom where
    foldLiteral :: (lit -> r) -> (Bool -> r) -> (atom -> r) -> lit -> r

zipLiterals :: IsLiteral lit atom =>
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
instance FirstOrderFormula fof atom v => IsLiteral fof atom v where
    foldLiteral neg tf at fm = foldFirstOrder qu co tf at fm
        where qu = error "instance IsLiteral FirstOrderFormula"
              co ((:~:) x) = neg x
              co _ = error "instance IsLiteral FirstOrderFormula"
    atomic = Data.Logic.Classes.FirstOrder.atomic
-}

toPropositional :: forall lit atom pf atom2. (IsLiteral lit atom, P.IsPropositional pf atom2) =>
                   (atom -> atom2) -> lit -> pf
toPropositional ca lit = foldLiteral (\ p -> (.~.) (toPropositional ca p)) fromBool (atomic . ca) lit

{-
prettyLit :: forall lit atom term v p f. (IsLiteral lit atom v, Apply atom p term, Term term v f) =>
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

prettyLit :: forall lit atom v. (IsLiteral lit atom) =>
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

fixityLiteral :: (IsLiteral formula atom) => formula -> Fixity
fixityLiteral formula =
    foldLiteral neg tf at formula
    where
      neg _ = Fixity 5 InfixN
      tf _ = Fixity 10 InfixN
      at = fixity

foldAtomsLiteral :: IsLiteral lit atom => (r -> atom -> r) -> r -> lit -> r
foldAtomsLiteral f i lit = foldLiteral (foldAtomsLiteral f i) (const i) (f i) lit
