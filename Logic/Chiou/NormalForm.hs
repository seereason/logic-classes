{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing #-}

{- NormalForm.hs -}
{- Charles Chiou -}

module Logic.Chiou.NormalForm
    ( ConjunctiveNormalForm(..)
    , ImplicativeNormalForm(..)
    , NormalSentence(..)
    , NormalTerm(..)
    , toSentence
    , fromSentence
    ) where

import Data.Generics (Data, Typeable)
import Logic.Clausal (Literal(..))
import Logic.Chiou.FirstOrderLogic (Sentence)
import qualified Logic.Chiou.FirstOrderLogic as F
import Logic.FirstOrder (FirstOrderLogic(..), InfixPred(..), Pretty, Term(..))
import qualified Logic.FirstOrder as Logic
import Logic.Implicative (Implicative(..))
import Logic.Instances.Chiou ()
import Logic.Logic (Logic(..), Boolean(..))

data ConjunctiveNormalForm v p f =
    CNF [NormalSentence v p f]
    deriving (Eq)

data ImplicativeNormalForm v p f
    = INF [NormalSentence v p f] [NormalSentence v p f]
    deriving (Eq, Show, Data, Typeable)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [NormalTerm v f]
    | NFEqual (NormalTerm v f) (NormalTerm v f)
    deriving (Eq, Ord, Show, Data, Typeable)

-- We need a distinct type here because of the functional dependencies
-- in class FirstOrderLogic.
data NormalTerm v f
    = Function f [NormalTerm v f]
    | Variable v
    deriving (Eq, Ord, Show, Data, Typeable)

instance Literal (NormalSentence v p f) where
    negate = NFNot
    negated (NFNot x) = not (negated x)
    negated _ = False

instance (FirstOrderLogic (Sentence v p f) (F.Term v f) v p f, Enum v, Ord p, Ord f) => Implicative (ImplicativeNormalForm v p f) (NormalSentence v p f) where
    neg (INF x _) = x
    pos (INF _ x) = x
    makeINF lhs rhs = INF lhs rhs

instance Logic (NormalSentence v p f) where
    (.~.) x   = NFNot x
    _ .|. _ = error "NormalSentence |"

instance (Logic (NormalSentence v p f), Logic.Term (NormalTerm v f) v f, Eq p, Boolean p, Data p, Pretty p, Pretty v, Pretty f) => FirstOrderLogic (NormalSentence v p f) (NormalTerm v f) v p f where
    for_all _ _ = error "FirstOrderLogic NormalSentence"
    exists _ _ = error "FirstOrderLogic NormalSentence"
    foldF n _ _ i p f =
        case f of
          NFNot x -> n x
          NFEqual t1 t2 -> i t1 (:=:) t2
          NFPredicate pr ts -> p pr ts
    zipF n _ _ i p f1 f2 =
        case (f1, f2) of
          (NFNot f1', NFNot f2') -> n f1' f2'
          (NFEqual f1l f1r, NFEqual f2l f2r) -> i f1l (:=:) f1r f2l (:=:) f2r
          (NFPredicate p1 ts1, NFPredicate p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp p args = NFPredicate p args
    x .=. y = NFEqual x y
    x .!=. y = NFNot (NFEqual x y)

instance (Ord v, Enum v, Data v, Eq f, Logic.Skolem f, Data f) => Logic.Term (NormalTerm v f) v f where
    var = Variable
    fApp = Function
    foldT v f t =
            case t of
              Variable x -> v x
              Function x ts -> f x ts
    zipT v fn t1 t2 =
        case (t1, t2) of
          (Variable x1, Variable x2) -> v x1 x2
          (Function f1 ts1, Function f2 ts2) -> fn f1 ts1 f2 ts2
          _ -> Nothing

toSentence :: FirstOrderLogic (Sentence v p f) (F.Term v f) v p f => NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (Ord v, Enum v, Data v, Eq f, Logic.Skolem f, Data f) => NormalTerm v f -> F.Term v f
toTerm (Function f ts) = Logic.fApp f (map toTerm ts)
toTerm (Variable v) = Logic.var v

fromSentence :: FirstOrderLogic (Sentence v p f) (F.Term v f) v p f => Sentence v p f -> NormalSentence v p f
fromSentence = foldF (NFNot . fromSentence)
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ _ _ _ -> error "fromSentence 2")
                 (\ t1 op t2 -> case op of
                                  (:=:) -> NFEqual (fromTerm t1) (fromTerm t2)
                                  _ -> error "fromSentence 3")
                 (\ p ts -> NFPredicate p (map fromTerm ts))


fromTerm :: (Ord v, Enum v, Data v, Eq f, Logic.Skolem f, Data f) => F.Term v f -> NormalTerm v f
fromTerm (F.Function f ts) = Function f (map fromTerm ts)
fromTerm (F.Variable v) = Variable v
