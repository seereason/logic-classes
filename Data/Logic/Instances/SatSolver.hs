{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.SatSolver where

import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean.SatSolver (Literal(Pos, Neg), CNF, newSatSolver, assertTrue', solve)
import Data.Generics (Data, Typeable)
import qualified Data.Set.Extra as S
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(..))
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import qualified Data.Logic.Classes.Literal as N
import Data.Logic.Classes.Negate (Negatable(..), negated, (.~.))
import Data.Logic.Classes.Propositional (PropositionalFormula)
import Data.Logic.Classes.Term (Term)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (LiteralMapT, NormalT)
import qualified Data.Map as M

instance Ord Literal where
    compare (Neg _) (Pos _) = LT
    compare (Pos _) (Neg _) = GT
    compare (Pos m) (Pos n) = compare m n
    compare (Neg m) (Neg n) = compare m n

instance Negatable Literal where
    negatePrivate (Neg x) = Pos x
    negatePrivate (Pos x) = Neg x
    foldNegation _ inverted (Neg x) = inverted (Pos x)
    foldNegation normal _ (Pos x) = normal (Pos x)

deriving instance Data Literal
deriving instance Typeable Literal

instance ClauseNormalFormula CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . null $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (Monad m,
          FirstOrderFormula formula atom v,
          PropositionalFormula formula atom,
          Atom atom term v,
          AtomEq atom p term,
          Term term v f,
          N.Literal formula atom,
          Ord formula) =>
         formula -> NormalT formula v term m CNF
toCNF f = clauseNormalForm f >>= S.ssMapM (lift . toLiteral) >>= return . makeCNF

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
