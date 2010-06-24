{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Predicate
    ( PredicateLogic(..)
    , Quant(..)
    , InfixPred(..)
    , freeVars
    , univquant_free_vars
    , substitute'
    , substitute
    , substituteTerm
    , substituteTerms
    , convertPred
    , convertTerm
    , toPropositional
    , normalize
    , module Logic.Propositional
    ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Data.Data (Data)
import Data.Function (on)
import Data.List (isPrefixOf, intercalate)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Data.String (IsString(..))
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Propositional

-- |Add quantifiers and terms and variables to the PropositionalLogic
-- class to get a PredicateLogic type class.  We need a new Fold
-- function here which adds a parameter to handle quantifier.  We also
-- override the default showForm method.  (No, we now add a new method.)
-- 
-- The functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error
-- 
--    No instance for (PropositionalLogic Formula t V p f)
-- 
-- because the function doesn't mention the Term type.
class (PropositionalLogic formula atom, Show v, Show p, Show f, Ord v, IsString v, IsString f) => PredicateLogic formula atom term v p f
                       | formula -> atom
                       , formula -> term
                       , formula -> v
                       , formula -> p
                       , term -> formula
                       , term -> v
                       , term -> f
                       , v -> formula
                       , v -> term
                       , v -> p
                       , v -> f where
    for_all :: [v] -> formula -> formula         -- ^ Universal quantification
    exists ::  [v] -> formula -> formula         -- ^ Existential quantification
    foldF :: (formula -> r)                         -- ^ Negation
          -> (Quant -> [v] -> formula -> r)         -- ^ Quantification
          -> (formula -> BinOp -> formula -> r) -- ^ Binary Operator
          -> (term -> InfixPred -> term -> r)       -- ^ Infix Predicate
          -> (p -> [term] -> r)                       -- ^ Atomic predicate application
          -> (formula)
          -> r                                           -- ^ Fold over the value of a formula
    foldT :: (v -> r)                                   -- ^ Variable
          -> (f -> [term] -> r)                       -- ^ Atomic function application
          -> term
          -> r                                           -- ^ Fold over the value of a term
    -- Helper functions for building folds: foldF (.~.) quant binOp infixPred pApp is a no-op
    quant :: Quant -> [v] -> formula -> formula
    quant All vs f = for_all vs f
    quant Exists vs f = exists vs f

    (.=.) :: term -> term -> formula             -- ^ Equality of Terms
    (.!=.) :: term -> term -> formula            -- ^ Inequality of Terms
    pApp :: p -> [term] -> formula                 -- ^ Predicate symbol application to terms

    var :: v -> term                                   -- ^ Variable
    fApp :: f -> [term] -> term                      -- ^ Function symbol application (constants are encoded as nullary functions)

    infixPred :: term -> InfixPred -> term -> formula
    infixPred t1 (:=:) t2 = t1 .=. t2
    infixPred t1 (:!=:) t2 = t1 .!=. t2

    showForm :: formula -> String
    showForm formula =
        foldF n q b i a formula
        where
          n f = "(.~.) " ++ parenForm f
          q All vs f = "for_all " ++ show vs ++ " " ++ parenForm f
          q Exists vs f = "exists " ++ show vs ++ " " ++ parenForm f
          b f1 op f2 = parenForm f1 ++ " " ++ showFormOp op ++ " " ++ parenForm f2
          i t1 op t2 = parenTerm t1 ++ " " ++ showTermOp op ++ " " ++ parenTerm t2
          a p ts = "pApp (" ++ show p ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"
          parenForm x = "(" ++ showForm x ++ ")"
          parenTerm x = "(" ++ showTerm x ++ ")"
          showFormOp (:<=>:) = ".<=>."
          showFormOp (:=>:) = ".=>."
          showFormOp (:&:) = ".&."
          showFormOp (:|:) = ".|."
          showTermOp (:=:) = ".=."
          showTermOp (:!=:) = ".!=."
    showTerm :: term -> String
    showTerm term =
              foldT v f term
              where
                v v' = "var " ++ show (toString v')
                f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"
    toString :: v -> String                     -- ^ Convert a v back into a string

-- * These three simple types could be parameters to the type class as
-- well instead of being implemented here concretely, but I'm not sure
-- whether the added complexity is worthwhile.
                       
-- | Quantifier specification
data Quant = All | Exists
              deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

-- | /Term -> Term -> Formula/ infix connectives
data InfixPred =
    (:=:) | (:!=:)         
            deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

instance Read InfixPred where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:=:), ":=:"),
                 ((:!=:), ":!=:")]

freeVars :: PredicateLogic formula atom term v p f => formula -> S.Set v
freeVars =
    foldF freeVars   
          (\_ vars x -> S.difference (freeVars x) (S.fromList vars))                    
          (\x _ y -> (mappend `on` freeVars) x y)
          (\x _ y -> (mappend `on` freeVarsOfTerm) x y)
          (\_ args -> S.unions (fmap freeVarsOfTerm args))

freeVarsOfTerm :: PredicateLogic formula atom term v p f => term -> S.Set v
freeVarsOfTerm =
    foldT S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: PredicateLogic formula atom term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else for_all (S.toList free) cnf'
    where free = freeVars cnf'

-- * Substituting variables

-- |Substitute new for each occurrence of old in a formula.
substitute' :: PredicateLogic formula atom term v p f => v -> v -> formula -> formula
substitute' new old formula =
    sf formula
    where
      sf f =
          foldF (\ f' -> (.~.) (sf f'))
                (\ q vs f' -> 
                     (case q of
                        All -> for_all
                        Exists -> exists) (map sv vs) (sf f'))
                (\ f1 op f2 ->
                      (case op of
                         (:<=>:) -> (.<=>.)
                         (:=>:) -> (.=>.)
                         -- (:<=:) -> (.<=.)
                         (:|:) -> (.|.)
                         (:&:) -> (.&.)
                         -- (:<~>:) -> (.<~>.)
                         -- (:~|:) -> (.~|.)
                         -- (:~&:) -> (.~&.)
                      ) (sf f1) (sf f2))
                 (\ t1 op t2 ->
                      (case op of
                         (:=:) -> (.=.)
                         (:!=:) -> (.!=.)) (st t1) (st t2))
                 (\ p ts ->
                      pApp p (map st ts))
                 f
      st t = foldT (var . sv) (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else v

-- |Substitute V for the (single) free variable in the formula.
substitute :: PredicateLogic formula atom term v p f => v -> formula -> formula
substitute new f =
    case S.toList (freeVars f) of
      [old] -> substitute' new old f
      _ -> error "subtitute: formula must have exactly one free variable"

substituteTerm :: (Eq term, PredicateLogic formula atom term v p f) => (term, term) -> formula -> formula
substituteTerm pair@(new, old) formula =
    foldF n q b i a formula
    where
      n = (.~.) . substituteTerm pair
      q All vs = for_all vs . substituteTerm pair
      q Exists vs = for_all vs . substituteTerm pair
      b f1 (:<=>:) f2 = substituteTerm pair f1 .<=>. substituteTerm pair f2
      b f1 (:=>:) f2 = substituteTerm pair f1 .=>. substituteTerm pair f2
      b f1 (:&:) f2 = substituteTerm pair f1 .&. substituteTerm pair f2
      b f1 (:|:) f2 = substituteTerm pair f1 .|. substituteTerm pair f2
      i t1 (:=:) t2 = st t1 .=. st t2
      i t1 (:!=:) t2 = st t1 .!=. st t2
      a p ts = pApp p (map st ts)
      st t = if t == old then new else t

substituteTerms :: (Eq term, PredicateLogic formula atom term v p f) => [(term, term)] -> formula -> formula
substituteTerms pairs formula = foldr substituteTerm formula pairs

-- |This is an example of a fold, though maybe handy.
normalize :: PredicateLogic formula atom term v p f => formula -> formula
normalize formula =
    foldF n q b i a formula
    where
      n = (.~.)
      q All = for_all
      q Exists = exists
      b f1 op f2 = foldF n q bRHS i a f2
          where
            bRHS f3 op2 f4 =
                if op == op2 && associative op
                then binOp (binOp f1 op f3) op f4
                else binOp f1 op (binOp f3 op2 f4)
      i = infixPred
      a = pApp
      associative op = op == (:&:) || op == (:|:)

-- |Convert any instance of a first order logic expression to any other.
convertPred :: forall formula1 atom1 term1 v1 p1 f1 formula2 atom2 term2 v2 p2 f2.
           (PredicateLogic formula1 atom1 term1 v1 p1 f1,
            PredicateLogic formula2 atom2 term2 v2 p2 f2) =>
           (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertPred convertV convertP convertF formula =
    foldF n q b i p formula
    where
      convert' = convertPred convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      n f = (.~.) (convert' f)
      q x vs f = quant x (map convertV vs) (convert' f)
      b f1 op f2 = binOp (convert' f1) op (convert' f2)
      i t1 op t2 = infixPred (convertTerm' t1) op (convertTerm' t2)
      p x ts = pApp (convertP x) (map convertTerm' ts)

convertTerm :: forall formula1 atom1 term1 v1 p1 f1 formula2 atom2 term2 v2 p2 f2.
               (PredicateLogic formula1 atom1 term1 v1 p1 f1,
                PredicateLogic formula2 atom2 term2 v2 p2 f2) =>
               (v1 -> v2) -> (f1 -> f2) -> term1 -> term2
convertTerm convertV convertF term =
    foldT v fn term
    where
      convertTerm' = convertTerm convertV convertF
      v = var . convertV
      fn x ts = fApp (convertF x) (map convertTerm' ts)

-- |Try to convert a first order logic formula to propositional.  This will
-- return Nothing if there are any 
toPropositional :: forall m formula1 atom1 term1 v1 p1 f1 formula2 atom2.
                   (Monad m, Applicative m, PredicateLogic formula1 atom1 term1 v1 p1 f1,
                    PropositionalLogic formula2 atom2) =>
                   (atom1 -> m atom2) -> formula1 -> m formula2
toPropositional convertA formula =
    foldF0 n b a formula
    where
      convert' = toPropositional convertA
      n f = (.~.) <$> convert' f
      b f1 op f2 = binOp <$> convert' f1 <*> pure op <*> convert' f2
      a atom = convertA atom >>= return . atomic

instance Version InfixPred
instance Version Quant

$(deriveSerialize ''InfixPred)
$(deriveSerialize ''Quant)

$(deriveNewData [''InfixPred, ''Quant])
