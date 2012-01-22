{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat0
    , plSat
    ) where

import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool, asBool))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula)
import Data.Logic.Classes.Formula (Formula(..))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Pretty (HasFixity(fixity), Pretty(pretty), topFixity)
import Data.Logic.Classes.Propositional (PropositionalFormula(..), clauseNormalForm', prettyPropositional, fixityPropositional, foldAtomsPropositional, mapAtomsPropositional)
import Data.Logic.Classes.Term (Term)
import Data.Logic.Harrison.Skolem (SkolemT)
import Data.Logic.Normal.Clause (clauseNormalForm)
import qualified Data.Set.Extra as S
import PropLogic

instance Negatable (PropForm a) where
    negatePrivate = N
    foldNegation normal inverted (N x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance {- Ord a => -} Combinable (PropForm a) where
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]

instance (Pretty a, HasFixity a, Ord a) => Formula (PropForm a) a where
    atomic = A
    foldAtoms = foldAtomsPropositional
    mapAtoms = mapAtomsPropositional

instance (Combinable (PropForm a), Pretty a, HasFixity a, Ord a) => PropositionalFormula (PropForm a) a where
    foldPropositional co tf at formula =
        case formula of
          -- EJ [x,y,z,...] -> CJ [EJ [x,y], EJ[y,z], ...]
          EJ [] -> error "Empty equijunct"
          EJ [x] -> foldPropositional co tf at x
          EJ [x0, x1] -> co (BinOp x0 (:<=>:) x1)
          EJ xs -> foldPropositional co tf at (CJ (map (\ (x0, x1) -> EJ [x0, x1]) (pairs xs)))
          SJ [] -> error "Empty subjunct"
          SJ [x] -> foldPropositional co tf at x
          SJ [x0, x1] -> co (BinOp x0 (:=>:) x1)
          SJ xs -> foldPropositional co tf at (CJ (map (\ (x0, x1) -> SJ [x0, x1]) (pairs xs)))
          DJ [] -> tf False
          DJ [x] -> foldPropositional co tf at x
          DJ (x0:xs) -> co (BinOp x0 (:|:) (DJ xs))
          CJ [] -> tf True
          CJ [x] -> foldPropositional co tf at x
          CJ (x0:xs) -> co (BinOp x0 (:&:) (CJ xs))
          N x -> co ((:~:) x)
          -- Not sure what to do about these - so far not an issue.
          T -> tf True
          F -> tf False
          A x -> at x

instance Constants (PropForm formula) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance (PropositionalFormula (PropForm atom) atom, Pretty atom, HasFixity atom) => Pretty (PropForm atom) where
    pretty = prettyPropositional pretty topFixity

instance (PropositionalFormula (PropForm atom) atom, HasFixity atom) => HasFixity (PropForm atom) where
    fixity = fixityPropositional

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

plSat0 :: (PropAlg a (PropForm formula), PropositionalFormula formula atom, Ord formula) => PropForm formula -> Bool
plSat0 f = satisfiable . (\ (x :: PropForm formula) -> x) . clauses0 $ f

clauses0 :: (PropositionalFormula formula atom, Ord formula) => PropForm formula -> PropForm formula
clauses0 f = CJ . map DJ . map S.toList . S.toList $ clauseNormalForm' f

plSat :: forall m formula atom term v f. (Monad m, FirstOrderFormula formula atom v, PropositionalFormula formula atom, Atom atom term v, Term term v f, Eq formula, Literal formula atom, Ord formula) =>
                formula -> SkolemT v term m Bool
plSat f = clauses f >>= (\ (x :: PropForm formula) -> return x) >>= return . satisfiable

clauses :: forall m formula atom term v f.
           (Monad m, FirstOrderFormula formula atom v, PropositionalFormula formula atom, Atom atom term v, Term term v f, Eq formula, Literal formula atom, Ord formula) =>
           formula -> SkolemT v term m (PropForm formula)
clauses f =
    do (cnf :: S.Set (S.Set formula)) <- clauseNormalForm f
       return . CJ . map DJ . map (map A) . map S.toList . S.toList $ cnf
