{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.PropLogic
    ( plSat
    ) where

import Data.Logic.NormalForm (clauseNormalForm)
import Data.Logic.FirstOrder
import Data.Logic.Monad (NormalT)
import Data.Logic.Normal (Literal)
import Data.Logic.Propositional.Instances.PropLogic ()
import qualified Data.Set.Extra as S
import PropLogic

plSat :: forall m formula term v p f. (Monad m, FirstOrderFormula formula term v p f, Ord formula, Literal formula term v p f) =>
                formula -> NormalT v term m Bool
plSat f = clauses f >>= (\ (x :: PropForm formula) -> return x) >>= return . satisfiable

clauses :: forall m formula term v p f. (Monad m, FirstOrderFormula formula term v p f, Literal formula term v p f) =>
           formula -> NormalT v term m (PropForm formula)
clauses f = clauseNormalForm f >>= return . CJ . map (DJ . map (toPropositional (A :: formula -> PropForm formula))) . map S.toList . S.toList
