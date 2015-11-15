{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, PackageImports, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Implicative
    ( LiteralMapT
    , NormalT
    , runNormal
    , runNormalT
    , ImplicativeForm(INF, neg, pos)
    , makeINF'
    , implicativeNormalForm
    , prettyINF
    , prettyProof
    ) where

import Control.Monad.Identity (Identity(runIdentity))
import Control.Monad.State (StateT(runStateT), MonadPlus, msum)
import Data.Bool (bool)
import Data.Generics (Data, Typeable, listify)
import Data.List as List (map)
import Data.Logic.ATP.Apply (HasApply(TermOf))
import Data.Logic.ATP.FOL (IsFirstOrder)
import Data.Logic.ATP.Formulas (IsFormula(AtomOf), true)
import Data.Logic.ATP.Lit (foldLiteral, IsLiteral, JustLiteral, LFormula)
import Data.Logic.ATP.Pretty (Pretty(pPrint))
import Data.Logic.ATP.Prop (IsPropositional, PFormula, simpcnf)
import Data.Logic.ATP.Quantified (IsQuantified(VarOf))
import Data.Logic.ATP.Skolem (HasSkolem(SVarOf, foldSkolem), runSkolem, runSkolemT, skolemize, SkolemT)
import Data.Logic.ATP.Term (IsFunction, IsTerm(FunOf))
import Data.Map as Map (empty, Map)
import Data.Set.Extra as Set (empty, flatten, fold, fromList, insert, map, Set, singleton, toList)
import Text.PrettyPrint ((<>), Doc, brackets, comma, hsep, parens, punctuate, text, vcat)

-- |Combination of Normal monad and LiteralMap monad
type NormalT lit m a = SkolemT (LiteralMapT lit m) (FunOf (TermOf (AtomOf lit))) a

runNormalT :: (Monad m, IsLiteral lit, IsFunction (FunOf (TermOf (AtomOf lit)))) => NormalT lit m a -> m a
runNormalT action = runLiteralMapM (runSkolemT action)

runNormal :: (IsLiteral lit, IsFunction (FunOf (TermOf (AtomOf lit)))) => NormalT lit Identity a -> a
runNormal = runIdentity . runNormalT

--type LiteralMap f = LiteralMapT f Identity
type LiteralMapT lit = StateT (Int, Map lit Int)

--runLiteralMap :: LiteralMap p a -> a
--runLiteralMap action = runIdentity (runLiteralMapM action)

runLiteralMapM :: Monad m => LiteralMapT f m a -> m a
runLiteralMapM action = (runStateT action) (1, Map.empty) >>= return . fst

-- |A type to represent a formula in Implicative Normal Form.  Such a
-- formula has the form @a & b & c .=>. d | e | f@, where a thru f are
-- literals.  One more restriction that is not implied by the type is
-- that no literal can appear in both the pos set and the neg set.
data ImplicativeForm lit =
    INF {neg :: Set lit, pos :: Set lit}
    deriving (Eq, Ord, Data, Typeable, Show)

-- |A version of MakeINF that takes lists instead of sets, used for
-- implementing a more attractive show method.
makeINF' :: (IsLiteral lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
makeINF' n p = INF (Set.fromList n) (Set.fromList p)

prettyINF :: (IsLiteral lit, Ord lit, Pretty lit) => ImplicativeForm lit -> Doc
prettyINF x = parens (hsep (List.map pPrint (Set.toList (neg x)))) <> text " => " <> parens (hsep (List.map pPrint (Set.toList (pos x))))

prettyProof :: (IsLiteral lit, Ord lit, Pretty lit) => Set (ImplicativeForm lit) -> Doc
prettyProof p = brackets (vcat (punctuate comma (List.map prettyINF (Set.toList p))))

instance (IsLiteral lit, Ord lit, Pretty lit) => Pretty (ImplicativeForm lit) where
    pPrint = prettyINF

-- |Take the clause normal form, and turn it into implicative form,
-- where each clauses becomes an (LHS, RHS) pair with the negated
-- literals on the LHS and the non-negated literals on the RHS:
-- @
--   (a | ~b | c | ~d) becomes (b & d) => (a | c)
--   (~b | ~d) | (a | c)
--   ~~(~b | ~d) | (a | c)
--   ~(b & d) | (a | c)
-- @
-- If there are skolem functions on the RHS, split the formula using
-- this identity:
-- @
--   (a | b | c) => (d & e & f)
-- @
-- becomes
-- @
--    a | b | c => d
--    a | b | c => e
--    a | b | c => f
-- @
implicativeNormalForm :: forall m fof pf lit atom term v function.
                         (IsFirstOrder fof, Ord fof,
                          IsPropositional pf,
                          JustLiteral lit,
                          HasSkolem function, Typeable function, Monad m,
                          atom ~ AtomOf fof,
                          pf ~ PFormula atom,
                          lit ~ LFormula atom, Data lit,
                          term ~ TermOf atom,
                          function ~ FunOf term,
                          v ~ VarOf fof,
                          v ~ SVarOf function) =>
                         fof -> SkolemT m function (Set (ImplicativeForm lit))
implicativeNormalForm formula =
    do let (cnf :: Set (Set (LFormula atom))) = simpcnf id (runSkolem (skolemize id formula) :: PFormula atom)
           pairs = Set.map (Set.fold collect (Set.empty, Set.empty)) cnf
           pairs' = Set.flatten (Set.map split pairs)
       return (Set.map (uncurry INF) pairs')
    where
      collect f (n, p) =
          foldLiteral (\ f' -> (Set.insert f' n, p))
                      (bool (Set.insert true n, p) (n, Set.insert true p))
                      (\ _ -> (n, Set.insert f p))
                      f
      split (lhs, rhs) =
          if any (foldSkolem (\_ -> False) (\_ _ -> True)) (gFind rhs :: [function])
          then Set.map (\ x -> (lhs, Set.singleton x)) rhs
          else Set.singleton (lhs, rhs)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . List.map return . listify (const True)
