{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
module Data.Logic.Instances.SatSolver where

import Apply (HasApply(PredOf, TermOf))
import Control.Monad.State (get, put)
import Control.Monad.Trans (lift)
import Data.Boolean (Literal(Pos, Neg), CNF)
import Data.Boolean.SatSolver (newSatSolver, assertTrue', solve)
import qualified Data.Map as M
import qualified Data.Set.Extra as S
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(..))
import Data.Logic.Normal.Implicative (LiteralMapT, NormalT)
import FOL (IsFirstOrder)
import Formulas (IsAtom, IsFormula(..))
import Lit (IsLiteral(..), negated, (.~.))
import Pretty (Associativity(InfixN), HasFixity(..), Pretty)
import Quantified (IsQuantified(VarOf))
import Skolem (simpcnf')
import Term (IsTerm(FunOf, TVarOf))

instance HasFixity Literal where
    precedence _ = 0
    associativity _ = InfixN

instance IsAtom Literal

instance IsFormula Literal where
    type AtomOf Literal = Int
    true = error "true :: IsLiteral"
    false = error "false :: IsLiteral"
    asBool _ = Nothing
    overatoms f (Pos x) r = f x r
    overatoms f (Neg x) r = f x r
    onatoms f (Pos x) = Pos (f x)
    onatoms f (Neg x) = Neg (f x)
    atomic = error "atomic"

instance IsLiteral Literal where
    naiveNegate (Pos x) = Neg x
    naiveNegate (Neg x) = Pos x
    foldNegation pos _ (Pos x) = pos (Pos x)
    foldNegation _ neg (Neg x) = neg (Pos x)
    foldLiteral' _ _ _ at (Pos x) = at x
    foldLiteral' _ ne _ _ (Neg x) = ne (Pos x)

instance ClauseNormalFormula CNF Literal where
    clauses = S.fromList . map S.fromList
    makeCNF = map S.toList . S.toList
    satisfiable cnf = return . not . (null :: [a] -> Bool) $ assertTrue' cnf newSatSolver >>= solve

toCNF :: (atom ~ AtomOf formula, p ~ PredOf atom, term ~ TermOf atom, v ~ VarOf formula, v ~ TVarOf term, function ~ FunOf term,
          Monad m,
          IsFirstOrder formula,
          -- IsAtomWithEquate atom p term,
          IsLiteral formula,
          Ord formula, Pretty formula) =>
         formula -> NormalT formula m CNF
toCNF f = S.ssMapM (lift . toLiteral) (simpcnf' f) >>= return . makeCNF

-- |Convert a [[formula]] to CNF, which means building a map from
-- formula to Literal.
toLiteral :: forall m lit. (Monad m, IsLiteral lit, Ord lit) =>
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
