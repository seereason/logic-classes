-- | 'FirstOrderFormula' is a multi-parameter type class for
-- representing instances of predicate or first order logic datatypes.
-- It builds on the 'Logic' class and adds the quantifiers @for_all@
-- and @exists@.  It also adds structure to the atomic formula
-- datatype: it introduces the @Term@ type and three type parameters:
-- @v@ (for variable), plus a @p@ parameter to represent the atomic
-- predicate type and an @f@ parameter to represent the type of the
-- atomic function type.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TemplateHaskell, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Wwarn #-}
module Logic.FirstOrder
    ( Skolem(..)
    , Arity(..)
    , Variable(..)
    , Predicate(..)
    , FirstOrderFormula(..)
    , Term(..)
    , Quant(..)
    , quant
    , (!), (?)
    , quant'
    , for_all'
    , exists'
    , showForm
    , showTerm
    , freeVars
    , quantVars
    , allVars
    , univquant_free_vars
    , substitute
    , substitutePairs
    , convertFOF
    , convertTerm
    , toPropositional
    , Pretty(..)
    , prettyForm
    , prettyTerm
    , disj
    , conj
    ) where

import Data.Data (Data)
import Data.Function (on)
import Data.List (intercalate, intersperse)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Logic
import Logic.Propositional (PropositionalFormula(..))
import Text.PrettyPrint

-- |A class for finding unused variable names.  The next method
-- returns the next in an endless sequence of variable names, if we
-- keep calling it we are bound to find some unused name.
class Variable v where
    next :: v -> v

class Pretty x where
    pretty :: x -> Doc

instance Pretty String where
    pretty = text

-- |This class shows how to convert between atomic Skolem functions
-- and Ints.
class Skolem f where
    toSkolem :: Int -> f
    fromSkolem  :: f -> Maybe Int

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldF and makes it easier to manage the
-- mapping of the different instances to the class methods.
data Predicate p term
    = Equal term term
    | NotEqual term term
    | Constant Bool
    | Apply p [term]    
    deriving (Eq, Ord, Show, Read, Data, Typeable)

class Arity p where
    -- |How many arguments does the predicate take?  Nothing
    -- means any number of arguments.
    arity :: p -> Maybe Int

class ( Ord v     -- Required so variables can be inserted into maps and sets
      , Variable v -- Used to rename variable during conversion to prenex
      , Data v    -- For serialization
      , Eq f      -- We need to check functions for equality during unification
      , Skolem f  -- Used to create skolem functions and constants
      , Data f    -- For serialization
      , Ord term  -- For implementing Ord in Literal
      ) => Term term v f | term -> v, term -> f where
    var :: v -> term
    -- ^ Build a term which is a variable reference.
    fApp :: f -> [term] -> term
    -- ^ Build a term by applying terms to an atomic function.  @f@
    -- (atomic function) is one of the type parameters, this package
    -- is mostly indifferent to its internal structure.
    foldT :: (v -> r) -> (f -> [term] -> r) -> term -> r
    -- ^ A fold for the term data type, which understands terms built
    -- from a variable and a term built from the application of a
    -- primitive function to other terms.
    zipT :: (v -> v -> Maybe r) -> (f -> [term] -> f -> [term] -> Maybe r) -> term -> term -> Maybe r

-- |The 'PropositionalFormula' type class.  Minimal implementation:
-- @for_all, exists, foldF, foldT, (.=.), pApp, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderFormula Formula term V p f)@ because the
-- function doesn't mention the Term type.
class ( Term term v f
      , Logic formula  -- Basic logic operations
      , Data formula   -- Allows us to use Data.Generics functions on formulas
      , Data p
      , Boolean p      -- To implement true and false below
      , Arity p        -- To decide how many arguments
      , Eq p           -- Required during resolution
      , Ord p
      , Ord f
      , Ord formula
      ) => FirstOrderFormula formula term v p f
                                    | formula -> term
                                    , term -> formula
                                    , formula -> p where
    -- | Universal quantification - for all x (formula x)
    for_all :: v -> formula -> formula
    -- | Existential quantification - there exists x such that (formula x)
    exists ::  v -> formula -> formula

    -- | A fold function similar to the one in 'PropositionalFormula'
    -- but extended to cover both the existing formula types and the
    -- ones introduced here.  @foldF (.~.) quant binOp infixPred pApp@
    -- is a no op.  The argument order is taken from Logic-TPTP.
    foldF :: (Quant -> v -> formula -> r)
          -> (Combine formula -> r)
          -> (Predicate p term -> r)
          -> formula
          -> r
    zipF :: (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
         -> (Combine formula -> Combine formula -> Maybe r)
         -> (Predicate p term -> Predicate p term -> Maybe r)
         -> formula -> formula -> Maybe r
    -- | Build a formula by applying zero or more terms to an atomic
    -- predicate.
    pApp :: p -> [term] -> formula
    -- | Equality of Terms
    (.=.) :: term -> term -> formula
    -- | Inequality of Terms
    (.!=.) :: term -> term -> formula
    a .!=. b = (.~.) (a .=. b)
    -- | The tautological formula
    true :: formula
    true = pApp (fromBool True) []
    -- | The inconsistant formula
    false :: formula
    false = pApp (fromBool False) []

-- |for_all with a list of variables, for backwards compatibility.
for_all' :: FirstOrderFormula formula term v p f => [v] -> formula -> formula
for_all' vs f = foldr for_all f vs

-- |exists with a list of variables, for backwards compatibility.
exists' :: FirstOrderFormula formula term v p f => [v] -> formula -> formula
exists' vs f = foldr for_all f vs

-- | Functions to disjunct or conjunct a list.
disj :: FirstOrderFormula formula term v p f => [formula] -> formula
disj [] = false
disj [x] = x
disj (x:xs) = x .|. disj xs

conj :: FirstOrderFormula formula term v p f => [formula] -> formula
conj [] = true
conj [x] = x
conj (x:xs) = x .&. conj xs

-- | Helper function for building folds.
quant :: FirstOrderFormula formula term v p f => 
         Quant -> v -> formula -> formula
quant All v f = for_all v f
quant Exists v f = exists v f

-- |Legacy version of quant from when we supported lists of quantified
-- variables.  It also has the virtue of eliding quantifications with
-- empty variable lists (by calling for_all' and exists'.)
quant' :: FirstOrderFormula formula term v p f => 
         Quant -> [v] -> formula -> formula
quant' All = for_all'
quant' Exists = exists'

-- | Display a formula in a format that can be read into the interpreter.
showForm :: forall formula term v p f. (FirstOrderFormula formula term v p f, Show v, Show p, Show f) => 
            formula -> String
showForm formula =
    foldF q c a formula
    where
      q All v f = "(for_all " ++ show v ++ " " ++ showForm f ++ ")"
      q Exists v f = "(exists " ++  show v ++ " " ++ showForm f ++ ")"
      c (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      c ((:~:) f) = "((.~.) " ++ showForm f ++ ")"
      a :: Predicate p term -> String
      a (Equal t1 t2) =
          "(" ++ parenTerm t1 ++ " .=. " ++ parenTerm t2 ++ ")"
      a (NotEqual t1 t2) =
          "(" ++ parenTerm t1 ++ " .!=. " ++ parenTerm t2 ++ ")"
      a (Constant x) = "pApp' (Constant " ++ show x ++ ")"
      a (Apply p ts) = "(pApp (" ++ show p ++ ") [" ++ intercalate "," (map showTerm ts) ++ "])"
      parenForm x = "(" ++ showForm x ++ ")"
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

showTerm :: forall term v f. (Term term v f, Show v, Show f) =>
            term -> String
showTerm term =
    foldT v f term
    where
      v :: v -> String
      v v' = "var (" ++ show v' ++ ")"
      f :: f -> [term] -> String
      f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"

prettyForm :: forall formula term v p f.
              (FirstOrderFormula formula term v p f, Term term v f, Pretty v, Pretty f, Pretty p) =>
              Int -> formula -> Doc
prettyForm prec formula =
    foldF (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop v <+> prettyForm 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyForm 3 f1 <+> formOp op <+> prettyForm 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyForm 4 f1 <+> formOp op <+> prettyForm 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyForm 5 f)
          pr
          formula
    where
      pr :: Predicate p term -> Doc
      pr (Constant x) = text (show x)
      pr (Equal t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "=" <+> prettyTerm t2)
      pr (NotEqual t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "!=" <+> prettyTerm t2)
      pr (Apply p ts) =
          pretty p <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map prettyTerm ts)))
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant All v = text {-"∀"-} "!" <> pretty v
      prettyQuant Exists v = text {-"∃"-} "?" <> pretty v
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

prettyTerm :: forall v f term. (Pretty f, Pretty v, Term term v f) => term -> Doc
prettyTerm t = foldT (pretty :: v -> Doc) (\ fn ts -> (pretty :: f -> Doc) fn <> brackets (hcat (intersperse (text ",") (map prettyTerm ts)))) t

-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = All | Exists deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

-- |Find the free (unquantified) variables in a formula.
freeVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
freeVars f =
    foldF (\_ v x -> S.delete v (freeVars x))                    
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` freeVars) x y
                 (:~:) f' -> freeVars f')
          (\ pa -> case pa of
                     Constant _ -> S.empty
                     Equal t1 t2 -> S.union (freeVarsOfTerm t1) (freeVarsOfTerm t2)
                     NotEqual t1 t2 -> S.union (freeVarsOfTerm t1) (freeVarsOfTerm t2)
                     Apply _ ts -> S.unions (fmap freeVarsOfTerm ts))
          f
    where
      freeVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- |Find the variables that are quantified in a formula
quantVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
quantVars =
    foldF (\ _ v x -> S.insert v (quantVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` quantVars) x y
                 ((:~:) f) -> quantVars f)
          (\ _ -> S.empty)

-- |Find the free and quantified variables in a formula.
allVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
allVars f =
    foldF (\_ v x -> S.insert v (allVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` allVars) x y
                 (:~:) f' -> freeVars f')
          (\ pa -> case pa of
                     Equal t1 t2 -> S.union (allVarsOfTerm t1) (allVarsOfTerm t2)
                     NotEqual t1 t2 -> S.union (allVarsOfTerm t1) (allVarsOfTerm t2)
                     Constant _ -> S.empty
                     Apply _ ts -> S.unions (fmap allVarsOfTerm ts))
          f
    where
      allVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: FirstOrderFormula formula term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else foldr for_all cnf' (S.toList free)
    where free = freeVars cnf'

-- |Replace each free occurrence of variable old with term new.
substitute :: FirstOrderFormula formula term v p f => v -> term -> formula -> formula
substitute old new formula =
    foldT (\ new' -> if old == new' then formula else substitute' formula)
          (\ _ _ -> substitute' formula)
          new
    where
      substitute' =
          foldF -- If the old variable appears in a quantifier
                -- we can stop doing the substitution.
                (\ q v f' -> quant q v (if old == v then f' else substitute' f'))
                (\ cm -> case cm of
                           ((:~:) f') -> combine ((:~:) (substitute' f'))
                           (BinOp f1 op f2) -> combine (BinOp (substitute' f1) op (substitute' f2)))
                (\ pa -> case pa of
                           Equal t1 t2 -> (st t1) .=. (st t2)
                           NotEqual t1 t2 -> (st t1) .!=. (st t2)
                           Constant x -> pApp (fromBool x) []
                           Apply p ts -> pApp p (map st ts))
      st t = foldT sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else var v

substitutePairs :: FirstOrderFormula formula term v p f => [(v, term)] -> formula -> formula
substitutePairs pairs formula = 
    foldr (\ (old, new) f -> substitute old new f) formula pairs 

-- |Convert any instance of a first order logic expression to any other.
convertFOF :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
              (FirstOrderFormula formula1 term1 v1 p1 f1,
               FirstOrderFormula formula2 term2 v2 p2 f2) =>
              (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertFOF convertV convertP convertF formula =
    foldF q c p formula
    where
      convert' = convertFOF convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      q x v f = quant x (convertV v) (convert' f)
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p (Equal t1 t2) = (convertTerm' t1) .=. (convertTerm' t2)
      p (NotEqual t1 t2) = (convertTerm' t1) .!=. (convertTerm' t2)
      p (Apply x ts) = pApp (convertP x) (map convertTerm' ts)
      p (Constant x) = pApp (fromBool x) []

convertTerm :: forall term1 v1 f1 term2 v2 f2.
               (Term term1 v1 f1,
                Term term2 v2 f2) =>
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
toPropositional :: forall formula1 term v p f formula2 atom.
                   (FirstOrderFormula formula1 term v p f,
                    PropositionalFormula formula2 atom) =>
                   (formula1 -> formula2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldF q c p formula
    where
      convert' = toPropositional convertAtom
      q _ _ _ = error "toPropositional: invalid argument"
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p _ = convertAtom formula

-- |Names for for_all and exists inspired by the conventions of the
-- TPTP project.
(!) :: FirstOrderFormula formula term v p f => v -> formula -> formula
(!) = for_all
(?) :: FirstOrderFormula formula term v p f => v -> formula -> formula
(?) = exists

instance Version Quant
instance Version (Predicate p term)

$(deriveSerialize ''Quant)
$(deriveSerialize ''Predicate)

$(deriveNewData [''Quant, ''Predicate])
