{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, UndecidableInstances #-}
{-# OPTIONS -Wall -Wwarn -fno-warn-name-shadowing #-}

{- NormalForm.hs -}
{- Charles Chiou -}

module Logic.Chiou.NormalForm
    ( ConjunctiveNormalForm(..)
    , ImplicativeNormalForm(..)
    , NormalSentence(..)
    , toNormal
    , toSentence
    ) where

import Data.Generics (Data, Typeable)
import Logic.Clausal (Literal(..))
import Logic.Chiou.FirstOrderLogic (Sentence(..), Term(..))
import Logic.FirstOrder (FirstOrderLogic(..), InfixPred(..))
import Logic.Implicative (Implicative(..))
import Logic.Instances.Chiou ()
import Logic.Logic (Logic(..))

data ConjunctiveNormalForm v p f =
    CNF [NormalSentence v p f]
    deriving (Eq)

data ImplicativeNormalForm v p f
    = INF [NormalSentence v p f] [NormalSentence v p f]
    deriving (Eq, Show, Data, Typeable)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [Term v f]
    | NFEqual (Term v f) (Term v f)
    deriving (Eq, Ord, Show, Data, Typeable)

instance Literal (NormalSentence v p f) where
    negate = NFNot
    negated (NFNot x) = not (negated x)
    negated _ = False

instance (FirstOrderLogic (Sentence v p f) (Term v f) v p f, Enum v, Ord p, Ord f) => Implicative (ImplicativeNormalForm v p f) (NormalSentence v p f) where
    neg (INF x _) = x
    pos (INF _ x) = x
    makeINF lhs rhs = INF lhs rhs

toSentence :: FirstOrderLogic (Sentence v p f) (Term v f) v p f => NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = t1 .=. t2
toSentence (NFPredicate p ts) = pApp p ts

toNormal :: FirstOrderLogic (Sentence v p f) (Term v f) v p f => Sentence v p f -> NormalSentence v p f
toNormal = foldF (NFNot . toNormal)
                 (\ _ _ _ -> error "toNormal 1")
                 (\ _ _ _ -> error "toNormal 2")
                 (\ t1 op t2 -> case op of
                                  (:=:) -> NFEqual t1 t2
                                  _ -> error "toNormal 3")
                 (\ p ts -> NFPredicate p ts)

