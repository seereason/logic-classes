{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans -Wall -Werror #-}
module Logic.Class
    ( Formulae(..)
    , Quant(..)
    , BinOp(..)
    , InfixPred(..)
    , freeVars
    , univquant_free_vars
    , substitute'
    , substitute
    , substituteTerm
    , substituteTerms
    , normalize
    ) where

import Data.Data (Data)
import Data.Function (on)
import Data.List (isPrefixOf, intercalate)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Data.String (IsString(..))
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)

-- |Formulae is a multi-parameter type class for representing first
-- order logic datatypes.  It is intended that we will be able to
-- write instances for various different implementations to allow
-- these systems to interoperate.  The class is patterned on the type
-- in the Logic-TPTP package.
-- 
-- The functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error
-- 
--    No instance for (Formulae Formula t V p f)
-- 
-- because the function doesn't mention the Term type.
class (Ord v, IsString v, IsString f, Show v, Show p, Show f) => Formulae formula term v p f
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
    for_all :: [v] -> formula -> formula         -- ^ Universal quantification
    (∀) :: v -> formula -> formula
    (∀) v f = for_all [v] f
    exists ::  [v] -> formula -> formula         -- ^ Existential quantification
    (∃) :: v -> formula -> formula
    (∃) v f = exists [v] f

    (.<=>.) :: formula -> formula -> formula -- ^ Equivalence
    (.=>.) :: formula -> formula -> formula  -- ^ Implication
    (.<=.) :: formula -> formula -> formula  -- ^ Reverse implication
    x .<=. y = y .=>. x
    (.|.) :: formula -> formula -> formula   -- ^ Disjunction/OR
    (.&.) :: formula -> formula -> formula   -- ^ Conjunction/AND
    (.<~>.) :: formula -> formula -> formula -- ^ XOR
    x .<~>. y = ((.~.) x .&. y) .|. (x .&. (.~.) y)
    (.~|.) :: formula -> formula -> formula  -- ^ NOR
    x .~|. y = (.~.) (x .|. y)
    (.~&.) :: formula -> formula -> formula  -- ^ NAND
    x .~&. y = (.~.) (x .&. y)
    (.~.) :: formula -> formula                  -- ^ Negation

    (.=.) :: term -> term -> formula             -- ^ Equality of Terms
    (.!=.) :: term -> term -> formula            -- ^ Inequality of Terms
    pApp :: p -> [term] -> formula                 -- ^ Predicate symbol application to terms

    var :: v -> term                                   -- ^ Variable
    fApp :: f -> [term] -> term                      -- ^ Function symbol application (constants are encoded as nullary functions)

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
    toString :: v -> String                     -- ^ Convert a v back into a string
    -- Helper functions for building folds: foldF (.~.) quant binOp infixPred pApp is a no-op
    quant :: Quant -> [v] -> formula -> formula
    quant All vs f = for_all vs f
    quant Exists vs f = exists vs f
    binOp :: formula -> BinOp -> formula -> formula
    binOp f1 (:<=>:) f2 = f1 .<=>. f2
    binOp f1 (:=>:) f2 = f1 .=>. f2
    -- binOp f1 (:<=:) f2 = f1 .<=. f2
    binOp f1 (:&:) f2 = f1 .&. f2
    binOp f1 (:|:) f2 = f1 .|. f2
    -- binOp f1 (:~&:) f2 = f1 .~&. f2
    -- binOp f1 (:~|:) f2 = f1 .~|. f2
    -- binOp f1 (:<~>:) f2 = f1 .<~>. f2
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

infixl 2  .<=>. ,  .=>. ,  .<~>.
infixl 3  .|.
infixl 4  .&.
infixl 5  .=. ,  .!=.

-- * These three simple types could be parameters to the type class as
-- well instead of being implemented here concretely, but I'm not sure
-- whether the added complexity is worthwhile.
                       
-- | Quantifier specification
data Quant = All | Exists
              deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

-- | Binary formula connectives 
data BinOp =
               (:<=>:)  -- ^ Equivalence
            |  (:=>:)  -- ^ Implication
            -- |  (:<=:)  -- ^ Reverse Implication
            |  (:&:)  -- ^ AND
            |  (:|:)  -- ^ OR
            -- |  (:~&:)  -- ^ NAND
            -- |  (:~|:)  -- ^ NOR
            -- |  (:<~>:)  -- ^ XOR
              deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- http://hackage.haskell.org/trac/ghc/ticket/4136
instance Read BinOp where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:<=>:), ":<=>:"),
                 -- ((:<~>:), ":<~>:"),
                 ((:=>:), ":=>:"),
                 -- ((:<=:), ":<=:"),
                 -- ((:~&:), ":~&:"),
                 -- ((:~|:), ":~|:"),
                 ((:&:), ":&:"),
                 ((:|:), ":|:")]

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

{-
instance (Formulae formula term v p f, Show (term), Show v, Show p, Show f) => Show formula where
    show = foldF (\ f' -> "(.~.) (" ++ show f' ++ ")")
                 (\ q vs f' -> show q ++ " [" ++ intercalate "," (map show vs) ++ "] (" ++ show f' ++ ")")
                 (\ f1 op f2 -> "(" ++ show f1 ++ ") " ++ show op ++ " (" ++ show f2 ++ ")")
                 (\ t1 op t2 -> "(" ++ show t1 ++ ") " ++ show op ++ " (" ++ show t2 ++ ")")
                 (\ p ts -> show p ++ " [" ++ intercalate "," (map show ts) ++ "]")
instance (Formulae formula term v p f, Show v, Show f) => Show term where
    show = foldT show (\ f ts -> show f ++ " [" ++ intercalate "," (map show ts) ++ "]")
-}

-- * Gathering free Variables
                              
{-
class FreeVars a where
    -- | Obtain the free variables from a formula or term
    freeVars :: a -> Set V
-}
             
freeVars :: Formulae formula term v p f => formula -> S.Set v
freeVars =
    foldF freeVars   
          (\_ vars x -> S.difference (freeVars x) (S.fromList vars))                    
          (\x _ y -> (mappend `on` freeVars) x y)
          (\x _ y -> (mappend `on` freeVarsOfTerm) x y)
          (\_ args -> S.unions (fmap freeVarsOfTerm args))

freeVarsOfTerm :: Formulae formula term v p f => term -> S.Set v
freeVarsOfTerm =
    foldT S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: Formulae formula term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else for_all (S.toList free) cnf'
    where free = freeVars cnf'

-- * Substituting variables

-- |Substitute new for each occurrence of old in a formula.
substitute' :: Formulae formula term v p f => v -> v -> formula -> formula
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
substitute :: Formulae formula term v p f => v -> formula -> formula
substitute new f =
    case S.toList (freeVars f) of
      [old] -> substitute' new old f
      _ -> error "subtitute: formula must have exactly one free variable"

substituteTerm :: (Eq term, Formulae formula term v p f) => (term, term) -> formula -> formula
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

substituteTerms :: (Eq term, Formulae formula term v p f) => [(term, term)] -> formula -> formula
substituteTerms pairs formula = foldr substituteTerm formula pairs

-- |This is an example of a fold, though maybe handy.
normalize :: Formulae formula term v p f => formula -> formula
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

instance Version InfixPred
instance Version BinOp
instance Version Quant

$(deriveSerialize ''InfixPred)
$(deriveSerialize ''BinOp)
$(deriveSerialize ''Quant)

$(deriveNewData [''InfixPred, ''BinOp, ''Quant])
