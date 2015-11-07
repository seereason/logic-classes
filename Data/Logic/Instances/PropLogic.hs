{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat
    ) where

import Data.Set.Extra as Set (toList)
import Formulas (BinOp(..), HasBoolean(fromBool, asBool), IsAtom, IsCombinable(..), IsFormula(..), IsNegatable(..))
import Lit (convertLiteral, IsLiteral(..), LFormula)
import Pretty (HasFixity(precedence, associativity), Pretty(pPrintPrec), Side(Top))
import Prop (associativityPropositional, IsPropositional(foldPropositional'), JustPropositional,
             precedencePropositional, prettyPropositional, simpcnf)
import PropLogic hiding (at)

instance IsAtom a => JustPropositional (PropForm a)

instance Ord a => IsNegatable (PropForm a) where
    naiveNegate = N
    foldNegation normal inverted (N x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Ord a => IsCombinable (PropForm a) where
    foldCombination = error "FIXME: PropForm foldCombination"
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]

instance IsAtom atom => IsLiteral (PropForm atom) where
    foldLiteral' ho ne tf at fm =
        case fm of
          N x -> ne x
          T -> tf True
          F -> tf False
          A x -> at x
          _ -> ho fm

instance IsAtom atom => IsFormula (PropForm atom) where
    type AtomOf (PropForm atom) = atom
    atomic = A
    overatoms = error "FIXME: overatoms PropForm"
    onatoms = error "FIXME: onatoms PropForm"

instance IsAtom atom => IsPropositional (PropForm atom) where
    foldPropositional' ho co ne tf at formula =
        case formula of
          -- EJ [x,y,z,...] -> CJ [EJ [x,y], EJ[y,z], ...]
          EJ [] -> error "Empty equijunct"
          EJ [x] -> foldPropositional' ho co ne tf at x
          EJ [x0, x1] -> co x0 (:<=>:) x1
          EJ xs -> foldPropositional' ho co ne tf at (CJ (map (\ (x0, x1) -> EJ [x0, x1]) (pairs xs)))
          SJ [] -> error "Empty subjunct"
          SJ [x] -> foldPropositional' ho co ne tf at x
          SJ [x0, x1] -> co x0 (:=>:) x1
          SJ xs -> foldPropositional' ho co ne tf at (CJ (map (\ (x0, x1) -> SJ [x0, x1]) (pairs xs)))
          DJ [] -> tf False
          DJ [x] -> foldPropositional' ho co ne tf at x
          DJ (x0:xs) -> co x0 (:|:) (DJ xs)
          CJ [] -> tf True
          CJ [x] -> foldPropositional' ho co ne tf at x
          CJ (x0:xs) -> co x0 (:&:) (CJ xs)
          N x -> ne x
          T -> tf True
          F -> tf False
          A x -> at x

instance HasBoolean (PropForm formula) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance (IsPropositional (PropForm atom), IsAtom atom) => Pretty (PropForm atom) where
    pPrintPrec = prettyPropositional Top

instance (IsPropositional (PropForm atom), IsAtom atom) => HasFixity (PropForm atom) where
    precedence = precedencePropositional
    associativity = associativityPropositional

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

{-
plSat0 :: (PropAlg a (PropForm atom), IsPropositional (PropForm atom) atom, Ord atom, Pretty atom, HasFixity atom) => PropForm atom -> Bool
plSat0 f = satisfiable . (\ (x :: PropForm atom) -> x) . clauses0 $ f

clauses0 :: (IsPropositional (PropForm atom) atom, Ord atom, Pretty atom, HasFixity atom) => PropForm atom -> PropForm atom
clauses0 = CJ . map (DJ . map unmarkLiteral . Set.toList) . Set.toList . simpcnf id
-}

plSat :: (IsPropositional (PropForm atom), IsAtom atom) => PropForm atom -> Bool
plSat = satisfiable . clauses

clauses :: forall atom. IsPropositional (PropForm atom) => PropForm atom -> PropForm atom
clauses = CJ . map (DJ . map (convertLiteral id :: LFormula atom -> PropForm atom) . Set.toList) . Set.toList . simpcnf id
