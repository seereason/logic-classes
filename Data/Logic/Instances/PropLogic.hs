{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( flatten
    , plSat0
    , plSat
    ) where

import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(fromBool))
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula, toPropositional)
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Propositional (PropositionalFormula(..), clauseNormalForm')
import Data.Logic.Classes.Term (Term)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Skolem (NormalT)
import qualified Data.Set.Extra as S
import PropLogic

instance Negatable (PropForm a) where
    (.~.) (N (N x)) = (.~.) x
    (.~.) (N x) = x
    (.~.) x = N x
    negated (N x) = not (negated x)
    negated _ = False

instance Ord a => Combinable (PropForm a) where
    x .<=>. y = EJ [x, y]
    x .=>.  y = SJ [x, y]
    x .|.   y = DJ [x, y]
    x .&.   y = CJ [x, y]

instance (Combinable (PropForm a), Ord a) => PropositionalFormula (PropForm a) a where
    atomic = A
    foldPropositional c a formula =
        case formula of
          -- EJ [x,y,z,...] -> CJ [EJ [x,y], EJ[y,z], ...]
          EJ [] -> error "Empty EJ"
          EJ [x] -> foldPropositional c a x
          EJ [x0, x1] -> c (BinOp x0 (:<=>:) x1)
          EJ xs -> foldPropositional c a (CJ (map (\ (x0, x1) -> EJ [x0, x1]) (pairs xs)))
          SJ [] -> error "Empty SJ"
          SJ [x] -> foldPropositional c a x
          SJ [x0, x1] -> c (BinOp x0 (:=>:) x1)
          SJ xs -> foldPropositional c a (CJ (map (\ (x0, x1) -> SJ [x0, x1]) (pairs xs)))
          DJ [] -> error "Empty disjunct"
          DJ [x] -> foldPropositional c a x
          DJ (x0:xs) -> c (BinOp x0 (:|:) (DJ xs))
          CJ [] -> error "Empty conjunct"
          CJ [x] -> foldPropositional c a x
          CJ (x0:xs) -> c (BinOp x0 (:&:) (CJ xs))
          N x -> c ((:~:) x)
          -- Not sure what to do about these - so far not an issue.
          T -> error "foldPropositional method of PropForm: T"
          F -> error "foldPropositional method of PropForm: F"
          A x -> a x

instance Constants (PropForm formula) where
    fromBool True = T
    fromBool False = F

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

plSat0 :: (PropAlg a (PropForm formula), PropositionalFormula formula atom) => PropForm formula -> Bool
plSat0 f = satisfiable . (\ (x :: PropForm formula) -> x) . clauses0 $ f

clauses0 :: PropositionalFormula formula atom => PropForm formula -> PropForm formula
clauses0 f = CJ . map DJ . map S.toList . S.toList $ clauseNormalForm' f

plSat :: forall m formula atom term v p f. (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Ord formula, Literal formula atom v, Constants p, Eq p) =>
                formula -> NormalT v term m Bool
plSat f = clauses f >>= (\ (x :: PropForm formula) -> return x) >>= return . satisfiable

clauses :: forall m formula atom term v p f. (Monad m, FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal formula atom v, Constants p, Eq p) =>
           formula -> NormalT v term m (PropForm formula)
clauses f = clauseNormalForm f >>= return . CJ . map (DJ . map (toPropositional (A :: formula -> PropForm formula))) . map S.toList . S.toList
