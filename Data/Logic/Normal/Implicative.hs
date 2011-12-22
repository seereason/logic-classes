{-# LANGUAGE DeriveDataTypeable, PackageImports, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wall #-}
module Data.Logic.Normal.Implicative
    ( ImplicativeForm(INF, neg, pos)
    , makeINF'
    , implicativeNormalForm
    , prettyINF
    , prettyProof
    ) where

import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Skolem (NormalT)

import "mtl" Control.Monad.State (MonadPlus, msum)
import Data.Generics (Data, Typeable, listify)
import Data.List (intersperse)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..))
import Data.Logic.Classes.Skolem (Skolem(fromSkolem))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import qualified Data.Set.Extra as Set
import Data.Maybe (isJust)
import Text.PrettyPrint (Doc, cat, text, hsep)

-- |A type to represent a formula in Implicative Normal Form.  Such a
-- formula has the form @a & b & c .=>. d | e | f@, where a thru f are
-- literals.  One more restriction that is not implied by the type is
-- that no literal can appear in both the pos set and the neg set.
data (Negatable lit, Ord lit) => ImplicativeForm lit =
    INF {neg :: Set.Set lit, pos :: Set.Set lit}
    deriving (Eq, Ord, Data, Typeable, Show)

-- |A version of MakeINF that takes lists instead of sets, used for
-- implementing a more attractive show method.
makeINF' :: (Negatable lit, Ord lit) => [lit] -> [lit] -> ImplicativeForm lit
makeINF' n p = INF (Set.fromList n) (Set.fromList p)

prettyINF :: (Negatable lit, Ord lit) => (lit -> Doc) -> ImplicativeForm lit -> Doc
prettyINF lit x = cat $ [text "(", hsep (map lit (Set.toList (neg x))),
                         text ") => (", hsep (map lit (Set.toList (pos x))), text ")"]

prettyProof :: (Negatable lit, Ord lit) => (lit -> Doc) -> Set.Set (ImplicativeForm lit) -> Doc
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
implicativeNormalForm :: forall m formula term v p f lit. 
                         (Monad m, FirstOrderFormula formula term v p f, Data formula, Literal lit term v p f) =>
                         formula -> NormalT v term m (Set.Set (ImplicativeForm lit))
implicativeNormalForm formula =
    do cnf <- clauseNormalForm formula
       let pairs = Set.map (Set.fold collect (Set.empty, Set.empty)) cnf :: Set.Set (Set.Set lit, Set.Set lit)
           pairs' = Set.flatten (Set.map split pairs) :: Set.Set (Set.Set lit, Set.Set lit)
       return (Set.map (\ (n,p) -> INF n p) pairs')
    -- clauseNormalForm formula >>= return . Set.unions . Set.map split . map (Set.fold collect (Set.empty, Set.empty))
    where
      collect :: lit -> (Set.Set lit, Set.Set lit) -> (Set.Set lit, Set.Set lit)
      collect f (n, p) =
          foldLiteral (\ f' -> (Set.insert f' n, p))
                      (\ _ -> (n, Set.insert f p))
                      f
      split :: (Set.Set lit, Set.Set lit) -> Set.Set (Set.Set lit, Set.Set lit)
      split (lhs, rhs) =
          if any isJust (map fromSkolem (gFind rhs :: [f]))
          then Set.map (\ x -> (lhs, Set.singleton x)) rhs
          else Set.singleton (lhs, rhs)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
