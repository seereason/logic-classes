{-# LANGUAGE DeriveDataTypeable, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Logic.Instances.SatSolver where

import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean.SatSolver
import Data.Generics (Data, Typeable)
import qualified Data.Map as M
import qualified Logic.Set as S
import Logic.FirstOrder (FirstOrderFormula(..))
import Logic.Logic (Negatable(..))
import Logic.Monad (NormalT', LiteralMapT)
import qualified Logic.Normal as N
import Logic.NormalForm (clauseNormalForm)

instance Ord Literal where
    compare (Neg _) (Pos _) = LT
    compare (Pos _) (Neg _) = GT
    compare (Pos m) (Pos n) = compare m n
    compare (Neg m) (Neg n) = compare m n

instance Negatable Literal where
    (.~.) (Pos n) = Neg n
    (.~.) (Neg n) = Pos n
    negated (Pos _) = False
    negated (Neg _) = True

deriving instance Data Literal
deriving instance Typeable Literal

instance N.ClauseNormalFormula CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . null $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (Monad m, FirstOrderFormula formula term v p f, N.Literal formula term v p f) =>
         formula -> NormalT' formula v term m CNF
toCNF f = clauseNormalForm id id id f >>= S.ssMapM (lift . toLiteral) >>= return . N.makeCNF

-- |Convert a [[formula]] to CNF, which means building a map from
-- formula to Literal.
toLiteral :: forall m lit. (Monad m, Negatable lit, Ord lit) =>
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
