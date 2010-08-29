{-# LANGUAGE DeriveDataTypeable, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Logic.Instances.SatSolver where

import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean.SatSolver
import Data.Generics (Data, Typeable)
import qualified Data.Map as M
import qualified Logic.Set as S
import Logic.FirstOrder (FirstOrderLogic(..))
import qualified Logic.Logic as L
import Logic.Monad (NormalT', LiteralMapT)
import Logic.Normal (ClauseNormal(..))
import Logic.NormalForm (clauseNormalForm)

instance Ord Literal where
    compare (Neg _) (Pos _) = LT
    compare (Pos _) (Neg _) = GT
    compare (Pos m) (Pos n) = compare m n
    compare (Neg m) (Neg n) = compare m n

instance L.Literal Literal where
    (.~.) (Pos n) = Neg n
    (.~.) (Neg n) = Pos n
    negated (Pos _) = False
    negated (Neg _) = True

deriving instance Data Literal
deriving instance Typeable Literal

instance ClauseNormal CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . null $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (Monad m, FirstOrderLogic formula term v p f) =>
         formula -> NormalT' formula v term m CNF
toCNF f = clauseNormalForm f >>= S.ssMapM (lift . toLiteral) >>= return . makeCNF

-- |Convert a [[formula]] to CNF, which means building a map from
-- formula to Literal.
toLiteral :: forall m lit. (Monad m, L.Literal lit, Ord lit) =>
             lit -> LiteralMapT lit m Literal
toLiteral f =
    literalNumber >>= return . if L.negated f then Neg else Pos
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
      f' = if L.negated f then (L..~.) f else f
