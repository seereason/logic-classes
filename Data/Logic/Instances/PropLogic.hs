{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat0
    , plSat
    ) where

import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(fromBool, asBool))
import Data.Logic.Classes.FirstOrder (IsQuantified)
import Data.Logic.Classes.Formula (IsFormula(..))
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (HasFixity(fixity), Pretty(pPrint), topFixity)
import Data.Logic.Classes.Propositional (IsPropositional(..), clauseNormalForm', prettyPropositional, fixityPropositional, overatomsPropositional, onatomsPropositional)
import Data.Logic.Classes.Term (IsTerm)
import Data.Logic.Harrison.Skolem (SkolemT)
import Data.Logic.Normal.Clause (clauseNormalForm)
import qualified Data.Set.Extra as S
import PropLogic

instance IsNegatable (PropForm a) where
    naiveNegate = N
    foldNegation normal inverted (N x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance {- Ord a => -} IsCombinable (PropForm a) where
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]

instance (Pretty a, HasFixity a, Ord a) => IsFormula (PropForm a) a where
    atomic = A
    overatoms = overatomsPropositional
    onatoms = onatomsPropositional

instance (IsCombinable (PropForm a), Pretty a, HasFixity a, Ord a) => IsPropositional (PropForm a) a where
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

instance HasBoolean (PropForm formula) where
    fromBool True = T
    fromBool False = F
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

instance (IsPropositional (PropForm atom) atom, Pretty atom, HasFixity atom) => Pretty (PropForm atom) where
    pPrint = prettyPropositional pPrint topFixity

instance (IsPropositional (PropForm atom) atom, HasFixity atom) => HasFixity (PropForm atom) where
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

plSat0 :: (PropAlg a (PropForm formula), IsPropositional formula atom, Ord formula) => PropForm formula -> Bool
plSat0 f = satisfiable . (\ (x :: PropForm formula) -> x) . clauses0 $ f

clauses0 :: (IsPropositional formula atom, Ord formula) => PropForm formula -> PropForm formula
clauses0 f = CJ . map DJ . map S.toList . S.toList $ clauseNormalForm' f

plSat :: forall m formula atom term v f. (Monad m, IsQuantified formula atom v, IsPropositional formula atom, Atom atom term v, IsTerm term v f, Eq formula, IsLiteral formula atom, Ord formula) =>
                formula -> SkolemT v term m Bool
plSat f = clauses f >>= (\ (x :: PropForm formula) -> return x) >>= return . satisfiable

clauses :: forall m formula atom term v f.
           (Monad m, IsQuantified formula atom v, IsPropositional formula atom, Atom atom term v, IsTerm term v f, Eq formula, IsLiteral formula atom, Ord formula) =>
           formula -> SkolemT v term m (PropForm formula)
clauses f =
    do (cnf :: S.Set (S.Set formula)) <- clauseNormalForm f
       return . CJ . map DJ . map (map A) . map S.toList . S.toList $ cnf
