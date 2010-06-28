-- | 'PredicateLogic' is a multi-parameter type class for representing
-- instances of predicate or first order logic datatypes.  It builds
-- on the 'PropositionalLogic' class and adds the quantifiers
-- @for_all@ and @exists@.  It also adds structure to the atomic
-- formula datatype: it introduces the @term@ and @v@ (for variable)
-- type parameters, plus a @p@ parameter to represent the atomic
-- predicate type and an @f@ parameter to represent the type of the
-- atomic function type.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.Predicate
    ( PredicateLogic(..)
    , Skolem(..)
    , Quant(..)
    , quant
    , InfixPred(..)
    , infixPred
    , showForm
    , freeVars
    , quantVars
    , allVars
    , univquant_free_vars
    , substitute'
    , substitute
    , substituteTerm
    , substituteTerms
    , convertPred
    , convertTerm
    , toPropositional
    , module Logic.Propositional
    ) where

import Control.Applicative (Applicative, (<$>), (<*>), pure)
import Data.Data (Data)
import Data.Function (on)
import Data.List (isPrefixOf, intercalate)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Logic
import Logic.Propositional

class Skolem v f where
    skolem :: v -> f

-- |The 'PropositionalLogic' type class.  Minimal implementation:
-- @for_all, exists, foldF, foldT, (.=.), (.!=.), pApp, fApp, var,
-- toString@.  The functional dependencies are necessary here so we
-- can write functions that don't fix all of the type parameters.  For
-- example, without them the univquant_free_vars function gives the
-- error @No instance for (PropositionalLogic Formula t V p f)@
-- because the function doesn't mention the Term type.
class (Logic formula, Ord v, Enum v, Skolem v f) =>
      PredicateLogic formula term v p f
                       | formula -> term
                       , formula -> v
                       , formula -> p
                       , term -> formula
                       , term -> v
                       , term -> f
                       , v -> formula
                       , v -> term
                       , v -> p
                       , v -> f where
    -- | Universal quantification - for all x (formula x)
    for_all :: [v] -> formula -> formula
    -- | Existential quantification - there exists x such that (formula x)
    exists ::  [v] -> formula -> formula

    -- | A fold function similar to the one in 'PropositionalLogic'
    -- but extended to cover both the existing formula types and the
    -- ones introduced here.  @foldF (.~.) quant binOp infixPred pApp@
    -- is a no op.  The argument order is taken from Logic-TPTP.
    foldF :: (formula -> r)
          -> (Quant -> [v] -> formula -> r)
          -> (formula -> BinOp -> formula -> r)
          -> (term -> InfixPred -> term -> r)
          -> (p -> [term] -> r)
          -> (formula)
          -> r
    -- |A fold for the term data type, which understands terms built
    -- from a variable and a term built from the application of a
    -- primitive function to other terms.
    foldT :: (v -> r)
          -> (f -> [term] -> r)
          -> term
          -> r
    -- | Equality of Terms
    (.=.) :: term -> term -> formula
    -- | Inequality of Terms
    (.!=.) :: term -> term -> formula
    -- | Build a formula by applying terms to an atomic predicate.
    pApp :: p -> [term] -> formula
    -- | Build a term which is a variable reference.
    var :: v -> term
    -- | Build a term by applying terms to an atomic function.  @f@
    -- (atomic function) is one of the type parameters, this package
    -- is mostly indifferent to its internal structure.
    fApp :: f -> [term] -> term


-- | Helper function for building folds.
quant :: PredicateLogic formula term v p f => 
         Quant -> [v] -> formula -> formula
quant All vs f = for_all vs f
quant Exists vs f = exists vs f

-- | Helper function for building folds.
infixPred :: PredicateLogic formula term v p f => 
             term -> InfixPred -> term -> formula
infixPred t1 (:=:) t2 = t1 .=. t2
infixPred t1 (:!=:) t2 = t1 .!=. t2

-- | Display a formula in a format that can be read into the interpreter.
showForm :: (PredicateLogic formula term v p f, Show v, Show p, Show f) => 
            formula -> String
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
      showTerm term =
          foldT v f term
          where
            v v' = "var " ++ show v'
            f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"
                       
-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = All | Exists deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

-- | /Term -> Term -> Formula/ infix connectives
data InfixPred = (:=:) | (:!=:) deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- <http://hackage.haskell.org/trac/ghc/ticket/4136>
instance Read InfixPred where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:=:), ":=:"),
                 ((:!=:), ":!=:")]

-- |Find the free (unquantified) variables in a formula.
freeVars :: PredicateLogic formula term v p f => formula -> S.Set v
freeVars =
    foldF freeVars   
          (\_ vars x -> S.difference (freeVars x) (S.fromList vars))                    
          (\x _ y -> (mappend `on` freeVars) x y)
          (\x _ y -> (mappend `on` freeVarsOfTerm) x y)
          (\_ args -> S.unions (fmap freeVarsOfTerm args))
    where
      freeVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- |Find the variables that are quantified in a formula
quantVars :: PredicateLogic formula term v p f => formula -> S.Set v
quantVars =
    foldF quantVars   
          (\ _ vars x -> S.union (S.fromList vars) (quantVars x))
          (\ x _ y -> (mappend `on` quantVars) x y)
          (\ _ _ _ -> S.empty)
          (\ _ _ -> S.empty)

-- |Find the free and quantified variables in a formula.
allVars :: PredicateLogic formula term v p f => formula -> S.Set v
allVars =
    foldF freeVars   
          (\_ vars x -> S.union (allVars x) (S.fromList vars))
          (\x _ y -> (mappend `on` allVars) x y)
          (\x _ y -> (mappend `on` allVarsOfTerm) x y)
          (\_ args -> S.unions (fmap allVarsOfTerm args))
    where
      allVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: PredicateLogic formula term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else for_all (S.toList free) cnf'
    where free = freeVars cnf'

-- * Substituting variables

-- |Substitute new for each free occurrence of old in a formula.
substitute' :: (PredicateLogic formula term v p f, Show formula) => v -> v -> formula -> formula
substitute' new old formula =
    foldF (\ f' -> (.~.) (sf f'))
              -- If the old variable appears in a quantifier
              -- we can stop doing the substitution.
              (\ q vs f' -> quant q vs (if elem old vs then f' else sf f'))
              (\ f1 op f2 -> binOp (sf f1) op (sf f2))
              (\ t1 op t2 -> infixPred (st t1) op (st t2))
              (\ p ts -> pApp p (map st ts))
              formula
    where
      sf = substitute' new old
      st t = foldT (var . sv) (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else v

-- |Substitute V for the (single) free variable in the formula.
substitute :: (PredicateLogic formula term v p f, Show formula) => v -> formula -> formula
substitute new f =
    case S.toList (freeVars f) of
      [old] -> substitute' new old f
      _ -> error "subtitute: formula must have exactly one free variable"

-- |Replace all occurrences of a term with another.
substituteTerm :: (Eq term, PredicateLogic formula term v p f) => (term, term) -> formula -> formula
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

-- |Call 'substituteTerm' for each of the @(new,old)@ pairs.
substituteTerms :: (Eq term, PredicateLogic formula term v p f) => [(term, term)] -> formula -> formula
substituteTerms pairs formula = foldr substituteTerm formula pairs

-- |Convert any instance of a first order logic expression to any other.
convertPred :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
           (PredicateLogic formula1 term1 v1 p1 f1,
            PredicateLogic formula2 term2 v2 p2 f2) =>
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

convertTerm :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
               (PredicateLogic formula1 term1 v1 p1 f1,
                PredicateLogic formula2 term2 v2 p2 f2) =>
               (v1 -> v2) -> (f1 -> f2) -> term1 -> term2
convertTerm convertV convertF term =
    foldT v fn term
    where
      convertTerm' = convertTerm convertV convertF
      v = var . convertV
      fn x ts = fApp (convertF x) (map convertTerm' ts)

-- |Try to convert a first order logic formula to propositional.  This
-- will return Nothing if there are any quantifiers, or if it runs
-- into an atom that it is unable to convert.
toPropositional :: forall m formula1 term v p f formula2 atom.
                   (PredicateLogic formula1 term v p f,
                    PropositionalLogic formula2 atom,
                    Monad m, Applicative m) =>
                   (formula1 -> m formula2) -> formula1 -> m formula2
toPropositional convertAtom formula =
    foldF n q b i p formula
    where
      convert' = toPropositional convertAtom
      n f = (.~.) <$> convert' f
      q _ _ _ = error "toPropositional: invalid argument"
      b f1 op f2 = binOp <$> convert' f1 <*> pure op <*> convert' f2
      i _ _ _ = convertAtom formula
      p _ _ = convertAtom formula

instance Version InfixPred
instance Version Quant

$(deriveSerialize ''InfixPred)
$(deriveSerialize ''Quant)

$(deriveNewData [''InfixPred, ''Quant])
