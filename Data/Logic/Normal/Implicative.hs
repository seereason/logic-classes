{-# LANGUAGE DeriveDataTypeable, PackageImports, RankNTypes, ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
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
import Data.Map as Map (empty, Map)
import Data.Maybe (isJust)
import Data.Set.Extra as Set (empty, flatten, fold, fromList, insert, map, Set, singleton, toList)
import FOL (IsFirstOrder, HasApply(TermOf, PredOf), IsQuantified(VarOf))
import Formulas (IsFormula(AtomOf), IsNegatable(..), true)
import Lib (Marked)
import Lit (convertLiteral, foldLiteral, IsLiteral)
import Pretty (Pretty(pPrint))
import Prop (Literal, Propositional, simpcnf)
import Skolem (HasSkolem(fromSkolem), runSkolem, runSkolemT, skolemize, SkolemT)
import Text.PrettyPrint ((<>), Doc, brackets, comma, hsep, parens, punctuate, text, vcat)

-- |Combination of Normal monad and LiteralMap monad
type NormalT formula v term m a = SkolemT (LiteralMapT formula m) a

runNormalT :: Monad m => NormalT formula v term m a -> m a
runNormalT action = runLiteralMapM (runSkolemT action)

runNormal :: NormalT formula v term Identity a -> a
runNormal = runIdentity . runNormalT

--type LiteralMap f = LiteralMapT f Identity
type LiteralMapT f = StateT (Int, Map f Int)

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
makeINF' :: (IsNegatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
makeINF' n p = INF (Set.fromList n) (Set.fromList p)

prettyINF :: (IsNegatable lit, Ord lit, Pretty lit) => ImplicativeForm lit -> Doc
prettyINF x = parens (hsep (List.map pPrint (Set.toList (neg x)))) <> text " => " <> parens (hsep (List.map pPrint (Set.toList (pos x))))

prettyProof :: (IsNegatable lit, Ord lit, Pretty lit) => Set (ImplicativeForm lit) -> Doc
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
{-
implicativeNormalForm :: forall m fof lit atom p term v f.
                         (IsFirstOrder fof atom p term v f, Ord fof,
                          IsLiteral lit atom, JustLiteral lit, Ord lit,
                          HasSkolem f v,
                          Monad m, Data lit, Typeable f) =>
                         fof -> SkolemT m (Set (ImplicativeForm lit))
-}
implicativeNormalForm :: forall m fof atom p term v f.
                         (atom ~ AtomOf fof, v ~ VarOf fof, term ~ TermOf atom, p ~ PredOf atom,
                          Monad m, Data fof, Pretty fof, Typeable f,
                          IsFirstOrder fof atom p term v f, Ord fof,
                          HasSkolem f v) => fof -> SkolemT m (Set (ImplicativeForm (Marked Literal fof)))
implicativeNormalForm formula =
    do let (cnf :: Set (Set (Marked Literal fof))) = (Set.map (Set.map convert) . simpcnf id) (runSkolem (skolemize id formula) :: Marked Propositional fof)
           pairs = Set.map (Set.fold collect (Set.empty, Set.empty)) cnf
           pairs' = Set.flatten (Set.map split pairs)
       return (Set.map (\ (n,p) -> INF n p) pairs')
    where
      convert :: Marked Literal (Marked Propositional fof) -> Marked Literal fof
      convert = convertLiteral id
      collect f (n, p) =
          foldLiteral (\ f' -> (Set.insert f' n, p))
                      (bool (Set.insert true n, p) (n, Set.insert true p))
                      (\ _ -> (n, Set.insert f p))
                      f
      split (lhs, rhs) =
          if any (isJust . fromSkolem) (gFind rhs :: [f])
          then Set.map (\ x -> (lhs, Set.singleton x)) rhs
          else Set.singleton (lhs, rhs)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . List.map return . listify (const True)
