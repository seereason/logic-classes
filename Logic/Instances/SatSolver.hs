{-# LANGUAGE DeriveDataTypeable, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
module Logic.Instances.SatSolver where

import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean.SatSolver
import Data.Generics (Data, Typeable)
import qualified Data.Map as M
import qualified Logic.Set as S
import qualified Logic.Clause as L
import Logic.FirstOrder (FirstOrderLogic(..))
import Logic.Monad (NormalT', LiteralMapT)
import Logic.NormalForm (clauseNormalForm)

instance Ord Literal where
    compare (Neg _) (Pos _) = LT
    compare (Pos _) (Neg _) = GT
    compare (Pos m) (Pos n) = compare m n
    compare (Neg m) (Neg n) = compare m n

instance L.Literal Literal where
    invert (Pos n) = Neg n
    invert (Neg n) = Pos n
    inverted (Pos n) = False
    inverted (Neg n) = True

deriving instance Data Literal
deriving instance Typeable Literal

instance L.ClauseNormal CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . null $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (Monad m, FirstOrderLogic formula term v p f, L.Literal formula) =>
         formula -> NormalT' formula v term m CNF
toCNF f = clauseNormalForm f >>= S.ssMapM (lift . toLiteral) >>= return . L.makeCNF

-- |Convert a [[formula]] to CNF, which means building a map from
-- formula to Literal.
toLiteral :: forall m formula. (Monad m, L.Literal formula) => formula -> LiteralMapT formula m Literal
toLiteral f =
    literalNumber f' >>= return . if L.inverted f then Neg else Pos
    where
      literalNumber :: formula -> LiteralMapT formula m Int
      literalNumber f' =
          get >>= \ (count, m) ->
          case M.lookup f' m of
            Nothing -> do let m' = M.insert f' count m
                          put (count+1, m') 
                          return count
            Just n -> return n
      f' :: formula
      f' = if L.inverted f then L.invert f else f
