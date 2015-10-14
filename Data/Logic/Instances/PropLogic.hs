{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat0
    , plSat
    ) where

--import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(fromBool, asBool))
--import Data.Logic.Classes.FirstOrder (IsQuantified)
import Data.Logic.Classes.Formula (IsFormula(..))
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (HasFixity(fixity), Pretty(pPrint), rootFixity)
import Data.Logic.Classes.Propositional (IsPropositional(..) {-, prettyPropositional, fixityPropositional, overatomsPropositional, onatomsPropositional-})
--import Data.Logic.Classes.Term (IsTerm)
import Data.Logic.Harrison.Skolem (SkolemT)
--import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Set.Extra as S (Set, toList)
import ATP (Side(Unary), prettyShow, simpcnf', IsFirstOrder)
import PropLogic hiding (at)

instance Ord a => IsNegatable (PropForm a) where
    naiveNegate = N
    foldNegation normal inverted (N x) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance Ord a => IsCombinable (PropForm a) where
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
    overatoms = error "overatomsPropositional"
    onatoms = error "onatomsPropositional"
    prettyFormula = error "FIXME"

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
    pPrint = prettyFormula rootFixity Unary

instance (IsPropositional (PropForm atom) atom, HasFixity atom) => HasFixity (PropForm atom) where
    fixity _ = rootFixity

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
clauses0 f = CJ . map DJ . map S.toList . S.toList $ (simpcnf' f :: Set (Set (PropForm atom)))

plSat :: forall m atom term v p f. (Monad m, IsFirstOrder (PropForm atom) atom p term v f, Eq atom, Ord atom) =>
                PropForm atom -> SkolemT m Bool
plSat f = clauses f >>= (\ (x :: PropForm atom) -> return x) >>= return . satisfiable

clauses :: forall m atom term v p f.
           (IsFirstOrder (PropForm atom) atom p term v f, Monad m, Eq atom, Ord atom) =>
           PropForm atom -> SkolemT m (PropForm atom)
clauses f =
    do let (cnf :: S.Set (S.Set (PropForm atom))) = simpcnf' f
       return . CJ . map DJ . map S.toList . S.toList $ cnf
