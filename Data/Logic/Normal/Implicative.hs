{-# LANGUAGE DeriveDataTypeable, PackageImports, RankNTypes, ScopedTypeVariables #-}
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
import Data.List (intersperse)
import Data.Logic.Classes.Atom (Atom)
import Data.Logic.Classes.Constants (true)
import Data.Logic.Classes.FirstOrder (IsQuantified(..))
import Data.Logic.Classes.Propositional (IsPropositional)
import Data.Logic.Classes.Skolem (HasSkolem(fromSkolem))
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Term (IsTerm)
import Data.Logic.Harrison.Skolem (SkolemT, runSkolemT)
import Data.Maybe (isJust)
import qualified Data.Set.Extra as Set
import qualified Data.Map as Map
import Text.PrettyPrint (Doc, cat, text, hsep)

-- |Combination of Normal monad and LiteralMap monad
type NormalT formula v term m a = SkolemT (LiteralMapT formula m) a

runNormalT :: Monad m => NormalT formula v term m a -> m a
runNormalT action = runLiteralMapM (runSkolemT action)

runNormal :: NormalT formula v term Identity a -> a
runNormal = runIdentity . runNormalT
 
--type LiteralMap f = LiteralMapT f Identity
type LiteralMapT f = StateT (Int, Map.Map f Int)

--runLiteralMap :: LiteralMap p a -> a
--runLiteralMap action = runIdentity (runLiteralMapM action)

runLiteralMapM :: Monad m => LiteralMapT f m a -> m a
runLiteralMapM action = (runStateT action) (1, Map.empty) >>= return . fst

-- |A type to represent a formula in Implicative Normal Form.  Such a
-- formula has the form @a & b & c .=>. d | e | f@, where a thru f are
-- literals.  One more restriction that is not implied by the type is
-- that no literal can appear in both the pos set and the neg set.
data ImplicativeForm lit =
    INF {neg :: Set.Set lit, pos :: Set.Set lit}
    deriving (Eq, Ord, Data, Typeable, Show)

-- |A version of MakeINF that takes lists instead of sets, used for
-- implementing a more attractive show method.
makeINF' :: (IsNegatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
makeINF' n p = INF (Set.fromList n) (Set.fromList p)

prettyINF :: (IsNegatable lit, Ord lit) => (lit -> Doc) -> ImplicativeForm lit -> Doc
prettyINF lit x = cat $ [text "(", hsep (map lit (Set.toList (neg x))),
                         text ") => (", hsep (map lit (Set.toList (pos x))), text ")"]

prettyProof :: (IsNegatable lit, Ord lit) => (lit -> Doc) -> Set.Set (ImplicativeForm lit) -> Doc
prettyProof lit p = cat $ [text "["] ++ intersperse (text ", ") (map (prettyINF lit) (Set.toList p)) ++ [text "]"]

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
implicativeNormalForm :: forall m formula atom term v f lit. 
                         (Monad m,
                          IsQuantified formula atom v,
                          IsPropositional formula atom,
                          Atom atom term v,
                          IsLiteral lit atom,
                          IsTerm term v f,
                          Data formula, Ord formula, Ord lit, Data lit, HasSkolem f v, Typeable f) =>
                         formula -> SkolemT m (Set.Set (ImplicativeForm lit))
implicativeNormalForm formula =
    do cnf <- {-clauseNormalForm-} undefined formula
       let pairs = Set.map (Set.fold collect (Set.empty, Set.empty)) cnf :: Set.Set (Set.Set lit, Set.Set lit)
           pairs' = Set.flatten (Set.map split pairs) :: Set.Set (Set.Set lit, Set.Set lit)
       return (Set.map (\ (n,p) -> INF n p) pairs')
    where
      collect :: lit -> (Set.Set lit, Set.Set lit) -> (Set.Set lit, Set.Set lit)
      collect f (n, p) =
          foldLiteral (\ f' -> (Set.insert f' n, p))
                      (bool (Set.insert true n, p) (n, Set.insert true p))
                      (\ _ -> (n, Set.insert f p))
                      f
      split :: (Set.Set lit, Set.Set lit) -> Set.Set (Set.Set lit, Set.Set lit)
      split (lhs, rhs) =
          if any (isJust . fromSkolem) (gFind rhs :: [f])
          then Set.map (\ x -> (lhs, Set.singleton x)) rhs
          else Set.singleton (lhs, rhs)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
