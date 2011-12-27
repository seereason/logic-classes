{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables #-}
module Data.Logic.Classes.Term
    ( Function(..)
    , Term(..)
    , convertTerm
    , showTerm
    , prettyTerm
    ) where

import Data.Generics (Data)
import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Skolem
import Data.Logic.Classes.Variable
import qualified Data.Set as Set
import Data.String (IsString(fromString))
import Text.PrettyPrint (Doc, (<>), brackets, hcat, text)

class (Ord f, IsString f) => Function f where
    variantF :: f -> Set.Set f -> f

class ( Function f
      , Ord v     -- Required so variables can be inserted into maps and sets
      , Variable v -- Used to rename variable during conversion to prenex
      , Data v    -- For serialization
      , Eq f      -- We need to check functions for equality during unification
      , Skolem f  -- Used to create skolem functions and constants
      , Data f    -- For serialization
      , Ord term  -- For implementing Ord in Literal
      ) => Term term v f | term -> v f where
    vt :: v -> term
    -- ^ Build a term which is a variable reference.
    fApp :: f -> [term] -> term
    -- ^ Build a term by applying terms to an atomic function.  @f@
    -- (atomic function) is one of the type parameters, this package
    -- is mostly indifferent to its internal structure.
    foldTerm :: (v -> r) -> (f -> [term] -> r) -> term -> r
    -- ^ A fold for the term data type, which understands terms built
    -- from a variable and a term built from the application of a
    -- primitive function to other terms.
    zipTerms :: (v -> v -> Maybe r) -> (f -> [term] -> f -> [term] -> Maybe r) -> term -> term -> Maybe r

    skolemConstant :: term -> v -> f -- ^ Term argument is just a proxy
    skolemFunction :: term -> v -> f

convertTerm :: forall term1 v1 f1 term2 v2 f2.
               (Term term1 v1 f1,
                Term term2 v2 f2) =>
               (v1 -> v2) -> (f1 -> f2) -> term1 -> term2
convertTerm convertV convertF term =
    foldTerm v fn term
    where
      convertTerm' = convertTerm convertV convertF
      v = vt . convertV
      fn x ts = fApp (convertF x) (map convertTerm' ts)

showTerm :: forall term v f. (Term term v f, Show v, Show f) =>
            term -> String
showTerm term =
    foldTerm v f term
    where
      v :: v -> String
      v v' = "vt (" ++ show v' ++ ")"
      f :: f -> [term] -> String
      f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"

prettyTerm :: forall v f term. (Term term v f) =>
              (v -> Doc)
           -> (f -> Doc)
           -> term
           -> Doc
prettyTerm pv pf t = foldTerm pv (\ fn ts -> pf fn <> brackets (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts)))) t
