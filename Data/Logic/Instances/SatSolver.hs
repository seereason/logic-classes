{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.SatSolver where

import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean (Literal(Pos, Neg), CNF)
import Data.Boolean.SatSolver (newSatSolver, assertTrue', solve)
import qualified Data.Map as M
import qualified Data.Set.Extra as S
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(..))
import Data.Logic.Normal.Implicative (LiteralMapT, NormalT)
import FOL (HasApplyAndEquate, IsFirstOrder)
import Formulas (IsNegatable(..), negated, (.~.))
import qualified Lit as N
import Pretty (Pretty)
import Skolem (simpcnf')

instance ClauseNormalFormula CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . (null :: [a] -> Bool) $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (Monad m,
          IsFirstOrder formula atom p term v f,
          -- IsAtomWithEquate atom p term,
          N.IsLiteral formula atom,
          Ord formula, Pretty formula) =>
         formula -> NormalT formula v term m CNF
toCNF f = S.ssMapM (lift . toLiteral) (simpcnf' f) >>= return . makeCNF

-- |Convert a [[formula]] to CNF, which means building a map from
-- formula to Literal.
toLiteral :: forall m lit. (Monad m, IsNegatable lit, Ord lit) =>
             lit -> LiteralMapT lit m Literal
toLiteral f =
    literalNumber >>= return . if negated f then Neg else Pos
    where
      literalNumber :: LiteralMapT lit m Int
      literalNumber =
          get >>= \ (count, m) ->
          case M.lookup f' m of
            Nothing -> do let m' = M.insert f' count m
                          put (count+1, m') 
                          return count
            Just n -> return n
      f' :: lit
      f' = if negated f then (.~.) f else f
