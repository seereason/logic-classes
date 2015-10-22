{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat0
    , plSat
    ) where

import Data.Set.Extra as Set (Set, empty, toList, union)
import FOL (IsFunction, HasFunctions(funcs), IsFirstOrder)
import Formulas (IsCombinable(..), Combination(..), BinOp(..), HasBoolean(fromBool, asBool), IsFormula(..), IsNegatable(..))
import Lit (IsLiteral(..))
import Pretty (HasFixity(fixity), Pretty(pPrint), rootFixity, prettyShow)
import Prop (foldPropositional, IsPropositional(foldPropositional'), JustPropositional)
import PropLogic hiding (at)
import Skolem (SkolemT, simpcnf')

instance JustPropositional (PropForm a)

instance Ord a => IsNegatable (PropForm a) where
    naiveNegate = N
    foldNegation' inverted normal (N x) = foldNegation' normal inverted x
    foldNegation' _ normal x = normal x

instance Ord a => IsCombinable (PropForm a) where
    foldCombination = error "FIXME: PropForm foldCombination"
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]

instance (Ord a, HasFixity a, Pretty a) => IsLiteral (PropForm a) a where
    foldLiteral ne tf at formula =
        case formula of
          N x -> ne x
          T -> tf True
          F -> tf False
          A x -> at x
          _ -> error ("Invalid PropForm literal: " ++ prettyShow formula)

instance (Pretty a, HasFixity a, Ord a) => IsFormula (PropForm a) a where
    atomic = A
    overatoms = error "FIXME: overatoms PropForm"
    onatoms = error "FIXME: onatoms PropForm"
    prettyFormula = error "FIXME prettyFormula PropForm"

instance (IsCombinable (PropForm a), Pretty a, HasFixity a, Ord a) => IsPropositional (PropForm a) a where
    foldPropositional' ho co tf at formula =
        case formula of
          -- EJ [x,y,z,...] -> CJ [EJ [x,y], EJ[y,z], ...]
          EJ [] -> error "Empty equijunct"
          EJ [x] -> foldPropositional' ho co tf at x
          EJ [x0, x1] -> co (BinOp x0 (:<=>:) x1)
          EJ xs -> foldPropositional' ho co tf at (CJ (map (\ (x0, x1) -> EJ [x0, x1]) (pairs xs)))
          SJ [] -> error "Empty subjunct"
          SJ [x] -> foldPropositional' ho co tf at x
          SJ [x0, x1] -> co (BinOp x0 (:=>:) x1)
          SJ xs -> foldPropositional' ho co tf at (CJ (map (\ (x0, x1) -> SJ [x0, x1]) (pairs xs)))
          DJ [] -> tf False
          DJ [x] -> foldPropositional' ho co tf at x
          DJ (x0:xs) -> co (BinOp x0 (:|:) (DJ xs))
          CJ [] -> tf True
          CJ [x] -> foldPropositional' ho co tf at x
          CJ (x0:xs) -> co (BinOp x0 (:&:) (CJ xs))
          N x -> co ((:~:) x)
          T -> tf True
          F -> tf False
          A x -> at x

instance HasBoolean (PropForm formula) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance (IsPropositional (PropForm atom) atom, Pretty atom, HasFixity atom) => Pretty (PropForm atom) where
    pPrint = prettyFormula

instance (IsPropositional (PropForm atom) atom, HasFixity atom) => HasFixity (PropForm atom) where
    fixity _ = rootFixity

instance (IsFunction function, HasFunctions atom function, Ord atom, Pretty atom, HasFixity atom) => HasFunctions (PropForm atom) function where
    funcs = foldPropositional co (const Set.empty) funcs
        where
          co ((:~:) fm) = funcs fm
          co (BinOp lhs _ rhs) = Set.union (funcs lhs) (funcs rhs)

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

plSat0 :: (PropAlg a (PropForm atom), IsFirstOrder (PropForm atom) atom p term v f, IsPropositional (PropForm atom) atom, Ord atom, Pretty atom) => PropForm atom -> Bool
plSat0 f = satisfiable . (\ (x :: PropForm atom) -> x) . clauses0 $ f

clauses0 :: forall atom p term v f. (IsFirstOrder (PropForm atom) atom p term v f, IsPropositional (PropForm atom) atom, Ord atom, Pretty atom) => PropForm atom -> PropForm atom
clauses0 f = CJ . map DJ . map Set.toList . Set.toList $ (simpcnf' f :: Set (Set (PropForm atom)))

plSat :: forall m atom term v p f. (Monad m, IsFirstOrder (PropForm atom) atom p term v f, Eq atom, Ord atom) =>
                PropForm atom -> SkolemT m Bool
plSat f = clauses f >>= (\ (x :: PropForm atom) -> return x) >>= return . satisfiable

clauses :: forall m atom term v p f.
           (IsFirstOrder (PropForm atom) atom p term v f, Monad m, Eq atom, Ord atom) =>
           PropForm atom -> SkolemT m (PropForm atom)
clauses f =
    do let (cnf :: Set (Set (PropForm atom))) = simpcnf' f
       return . CJ . map DJ . map Set.toList . Set.toList $ cnf
