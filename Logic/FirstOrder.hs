-- | 'FirstOrderLogic' is a multi-parameter type class for
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
    , FirstOrderLogic(..)
    , Term(..)
    , Quant(..)
    , quant
    , InfixPred(..)
    , infixPred
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
import Data.List (isPrefixOf, intercalate, intersperse)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Data.String (IsString)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Logic
import Logic.Propositional (PropositionalLogic(..))
import Text.PrettyPrint

class Pretty x where
    pretty :: x -> Doc

instance Pretty String where
    pretty = text

-- |This class shows how to convert between atomic Skolem functions
-- and Ints.
class Skolem f where
    toSkolem :: Int -> f
    fromSkolem  :: f -> Maybe Int

class (Ord v, Enum v, Data v,
       Eq f, Skolem f, Data f) => Term term v f | term -> v, term -> f where
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

-- |The 'PropositionalLogic' type class.  Minimal implementation:
-- @for_all, exists, foldF, foldT, (.=.), pApp, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderLogic Formula term V p f)@ because the
-- function doesn't mention the Term type.
class (Ord v, IsString v, Pretty v, Show v, 
       Ord p, IsString p, Boolean p, Data p, Pretty p,
       Ord f, IsString f, Pretty f,
       Logic formula, Ord formula, Data formula, Show formula, Eq term,
       Term term v f) => FirstOrderLogic formula term v p f
                       | formula -> term
                       , formula -> v
                       , formula -> p
                       , term -> formula
                       , term -> v
                       , term -> f where
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
    zipF :: (formula -> formula -> Maybe r)
         -> (Quant -> [v] -> formula -> Quant -> [v] -> formula -> Maybe r)
         -> (formula -> BinOp -> formula -> formula -> BinOp -> formula -> Maybe r)
         -> (term -> InfixPred -> term -> term -> InfixPred -> term -> Maybe r)
         -> (p -> [term] -> p -> [term] -> Maybe r)
         -> formula -> formula -> Maybe r
    -- | Equality of Terms
    (.=.) :: term -> term -> formula
    -- | Inequality of Terms
    (.!=.) :: term -> term -> formula
    a .!=. b = (.~.) (a .=. b)
    -- | Build a formula by applying terms to an atomic predicate.
    pApp :: p -> [term] -> formula

-- | Functions to 
disj :: FirstOrderLogic formula term v p f => [formula] -> formula
disj [] = pApp (fromBool False) []
disj [x] = x
disj (x:xs) = x .|. disj xs

conj :: FirstOrderLogic formula term v p f => [formula] -> formula
conj [] = pApp (fromBool True) []
conj [x] = x
conj (x:xs) = x .&. conj xs

-- | Helper function for building folds.
quant :: FirstOrderLogic formula term v p f => 
         Quant -> [v] -> formula -> formula
quant All vs f = for_all vs f
quant Exists vs f = exists vs f

-- | Helper function for building folds.
infixPred :: FirstOrderLogic formula term v p f => 
             term -> InfixPred -> term -> formula
infixPred t1 (:=:) t2 = t1 .=. t2
infixPred t1 (:!=:) t2 = t1 .!=. t2

-- | Display a formula in a format that can be read into the interpreter.
showForm :: forall formula term v p f. (FirstOrderLogic formula term v p f, Show v, Show p, Show f) => 
            formula -> String
showForm formula =
    foldF n q b i a formula
    where
      n f = "((.~.) " ++ showForm f ++ ")"
      q All vs f = "(for_all [" ++ intercalate "," (map show vs) ++ "] " ++ showForm f ++ ")"
      q Exists vs f = "(exists [" ++ intercalate "," (map show vs) ++ "] " ++ showForm f ++ ")"
      b f1 op f2 = "(" ++ showForm f1 ++ " " ++ showFormOp op ++ " " ++ parenForm f2 ++ ")"
      i :: term -> InfixPred -> term -> String
      i t1 op t2 = "(" ++ parenTerm t1 ++ " " ++ showTermOp op ++ " " ++ parenTerm t2 ++ ")"
      a :: p -> [term] -> String
      a p ts = "(pApp (" ++ show p ++ ") [" ++ intercalate "," (map showTerm ts) ++ "])"
      parenForm x = "(" ++ showForm x ++ ")"
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"
      showFormOp (:<=>:) = ".<=>."
      showFormOp (:=>:) = ".=>."
      showFormOp (:&:) = ".&."
      showFormOp (:|:) = ".|."
      showTermOp (:=:) = ".=."
      showTermOp (:!=:) = ".!=."

showTerm :: forall formula term v p f. (FirstOrderLogic formula term v p f, Show v, Show p, Show f) => 
            term -> String
showTerm term =
    foldT v f term
    where
      v :: v -> String
      v v' = "var (" ++ show v' ++ ")"
      f :: f -> [term] -> String
      f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"

prettyForm :: forall formula term v p f.
              (FirstOrderLogic formula term v p f, Term term v f, Pretty v, Pretty f, Pretty p) =>
              Int -> formula -> Doc
prettyForm prec formula =
    foldF (\ f -> text {-"¬"-} "~" <> prettyForm 5 f)
          (\ qop vs f -> parensIf (prec > 1) $ hsep (map (prettyQuant qop) vs) <+> prettyForm 1 f)
          (\ f1 op f2 ->
               case op of
                 (:=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                 (:<=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                 (:&:) -> parensIf (prec > 3) $ (prettyForm 3 f1 <+> formOp op <+> prettyForm 3 f2)
                 (:|:) -> parensIf {-(prec > 4)-} True $ (prettyForm 4 f1 <+> formOp op <+> prettyForm 4 f2))
          i
          pr
          formula
    where
      i :: term -> InfixPred -> term -> Doc
      i t1 op t2 = parensIf (prec > 6) (prettyTerm t1 <+> termOp op <+> prettyTerm t2)
      pr :: p -> [term] -> Doc
      pr p ts = pretty p <> case ts of
                              [] -> empty
                              _ -> parens (hcat (intersperse (text ",") (map prettyTerm ts)))
      -- parenForm x = parens (prettyForm x)
      -- parenTerm x = parens (term x)
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant All v = text {-"∀"-} "!" <> pretty v
      prettyQuant Exists v = text {-"∃"-} "?" <> pretty v
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"
      termOp (:=:) = text "="
      termOp (:!=:) = text "!="

prettyTerm :: forall v f term. (Pretty f, Pretty v, Term term v f) => term -> Doc
prettyTerm t = foldT (pretty :: v -> Doc) (\ fn ts -> (pretty :: f -> Doc) fn <> brackets (hcat (intersperse (text ",") (map prettyTerm ts)))) t

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
freeVars :: FirstOrderLogic formula term v p f => formula -> S.Set v
freeVars f =
    foldF freeVars   
          (\_ vars x -> S.difference (freeVars x) (S.fromList vars))                    
          (\x _ y -> (mappend `on` freeVars) x y)
          (\x _ y -> (mappend `on` freeVarsOfTerm) x y)
          (\_ args -> S.unions (fmap freeVarsOfTerm args))
          f
    where
      freeVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- |Find the variables that are quantified in a formula
quantVars :: FirstOrderLogic formula term v p f => formula -> S.Set v
quantVars =
    foldF quantVars   
          (\ _ vars x -> S.union (S.fromList vars) (quantVars x))
          (\ x _ y -> (mappend `on` quantVars) x y)
          (\ _ _ _ -> S.empty)
          (\ _ _ -> S.empty)

-- |Find the free and quantified variables in a formula.
allVars :: FirstOrderLogic formula term v p f => formula -> S.Set v
allVars f =
    foldF freeVars   
          (\_ vars x -> S.union (allVars x) (S.fromList vars))
          (\x _ y -> (mappend `on` allVars) x y)
          (\x _ y -> (mappend `on` allVarsOfTerm) x y)
          (\_ args -> S.unions (fmap allVarsOfTerm args))
          f
    where
      allVarsOfTerm = foldT S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: FirstOrderLogic formula term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else for_all (S.toList free) cnf'
    where free = freeVars cnf'

-- |Replace each free occurrence of variable old with term new.
substitute :: FirstOrderLogic formula term v p f => v -> term -> formula -> formula
substitute old new formula | var old == new = formula
substitute old new formula =
    foldF (\ f' -> (.~.) (sf f'))
              -- If the old variable appears in a quantifier
              -- we can stop doing the substitution.
              (\ q vs f' -> quant q vs (if elem old vs then f' else sf f'))
              (\ f1 op f2 -> binOp (sf f1) op (sf f2))
              (\ t1 op t2 -> infixPred (st t1) op (st t2))
              (\ p ts -> pApp p (map st ts))
              formula
    where
      sf = substitute old new
      st t = foldT sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else var v

substitutePairs :: FirstOrderLogic formula term v p f => [(v, term)] -> formula -> formula
substitutePairs pairs formula = 
    foldr (\ (old, new) f -> substitute old new f) formula pairs 

-- |Convert any instance of a first order logic expression to any other.
convertFOF :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
              (FirstOrderLogic formula1 term1 v1 p1 f1,
               FirstOrderLogic formula2 term2 v2 p2 f2) =>
              (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertFOF convertV convertP convertF formula =
    foldF n q b i p formula
    where
      convert' = convertFOF convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      n f = (.~.) (convert' f)
      q x vs f = quant x (map convertV vs) (convert' f)
      b f1 op f2 = binOp (convert' f1) op (convert' f2)
      i t1 op t2 = infixPred (convertTerm' t1) op (convertTerm' t2)
      p x ts = pApp (convertP x) (map convertTerm' ts)

convertTerm :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
               (FirstOrderLogic formula1 term1 v1 p1 f1,
                FirstOrderLogic formula2 term2 v2 p2 f2) =>
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
                   (FirstOrderLogic formula1 term v p f,
                    PropositionalLogic formula2 atom) =>
                   (formula1 -> formula2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldF n q b i p formula
    where
      convert' = toPropositional convertAtom
      n f = (.~.) (convert' f)
      q _ _ _ = error "toPropositional: invalid argument"
      b f1 op f2 = binOp (convert' f1) op (convert' f2)
      i _ _ _ = convertAtom formula
      p _ _ = convertAtom formula

instance Version InfixPred
instance Version Quant

$(deriveSerialize ''InfixPred)
$(deriveSerialize ''Quant)

$(deriveNewData [''InfixPred, ''Quant])
