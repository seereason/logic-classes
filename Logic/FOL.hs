{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- |Yet another set of first order logic types.  The intent is to
-- convert back and forth from the types used by other software we
-- might decide to use, and to have this format which fills our
-- particular needs - use of Data.Text instead of string, and more
-- abstraction of the primitive values.  Patterned after Logic-TPTP.
module Logic.FOL
    ( Formula(..)
    , Term(..)
    , BinOp(..)
    , InfixPred(..)
    , Quant(..)
    , V(..)
    , AtomicPredicate'
    , AtomicFunction'
    , Proposition
    , Predicate
    , pApp
    , var
    , fApp
    , numberLitTerm
    , distinctObjectTerm
    , FreeVars(freeVars)
    , univquant_free_vars
    , substitute
    , substitute'
    , module Logic.AtomicFunction
    , module Logic.AtomicPredicate
    , module Logic.AtomicWord
    , module Logic.Classes
    , ) where

import Data.Data (Data)
import Data.Function (on)
import Data.List (isPrefixOf)
import Data.Monoid (Monoid(..))
import Data.Set (Set)
import qualified Data.Set as S
import Data.String (IsString)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import qualified Happstack.Facebook.Common as Facebook
import Logic.AtomicFunction (AtomicFunction(..))
import Logic.AtomicPredicate (AtomicPredicate(..))
import Logic.AtomicWord (AtomicWord(..))
import Logic.Classes

-- * Types

type AtomicPredicate' = AtomicPredicate Facebook.User Predicate AtomicWord
type AtomicFunction' = AtomicFunction AtomicWord
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula
    = PredApp AtomicPredicate' [Term] -- ^ Predicate application.  The terms are the free variables.
    | (:~:) Formula                   -- ^ Negation
    | BinOp Formula BinOp Formula     -- ^ Binary connective application
    | InfixPred Term InfixPred Term   -- ^ Infix predicate application (equalities, inequalities)
    | Quant Quant [V] Formula         -- ^ Quantified formula
    deriving (Eq,Ord,Show,Read,Data,Typeable)

type Predicate = Formula
type Proposition = Formula

-- | Binary formula connectives 
data BinOp =
               (:<=>:)  -- ^ Equivalence
            |  (:=>:)  -- ^ Implication
            |  (:<=:)  -- ^ Reverse Implication
            |  (:&:)  -- ^ AND
            |  (:|:)  -- ^ OR
            |  (:~&:)  -- ^ NAND
            |  (:~|:)  -- ^ NOR
            |  (:<~>:)  -- ^ XOR
              deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- http://hackage.haskell.org/trac/ghc/ticket/4136
instance Read BinOp where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:<=>:), ":<=>:"),
                 ((:<~>:), ":<~>:"),
                 ((:=>:), ":=>:"),
                 ((:<=:), ":<=:"),
                 ((:~&:), ":~&:"),
                 ((:~|:), ":~|:"),
                 ((:&:), ":&:"),
                 ((:|:), ":|:")]

-- | The range of a term is an element of a set.
data Term
    = Var V                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp AtomicFunction' [Term] -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    | NumberLitTerm Double          -- ^ Number literal
    | DistinctObjectTerm String     -- ^ Double-quoted item
    deriving (Eq,Ord,Show,Read,Data,Typeable)

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
                       
-- | Quantifier specification
data Quant = All | Exists
              deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)
                
-- | Variable names
newtype V = V String
    deriving (Eq,Ord,Show,Data,Typeable,Read,Monoid,IsString)

-- * Formula Combinators

instance FormulaC Formula Term V where
    for_all vars x = Quant All vars x       -- ^ Universal quantification
    exists vars x = Quant Exists vars x     -- ^ Existential quantification
    x .<=>. y = BinOp  x (:<=>:) y          -- ^ Equivalence
    x .=>.  y = BinOp  x (:=>:)  y          -- ^ Implication
    x .<=.  y = BinOp  x (:<=:)  y          -- ^ Reverse implication
    x .|.   y = BinOp  x (:|:)   y          -- ^ Disjunction/OR
    x .&.   y = BinOp  x (:&:)   y          -- ^ Conjunction/AND
    x .<~>. y = BinOp  x (:<~>:) y          -- ^ XOR
    x .~|.  y = BinOp  x (:~|:)  y          -- ^ NOR
    x .~&.  y = BinOp  x (:~&:)  y          -- ^ NAND
    (.~.) x   = (:~:) x                     -- ^ Negation
    -- * Formula Builders
    x .=. y   = InfixPred x (:=:)   y       -- ^ Equality of Terms
    x .!=. y  = InfixPred x (:!=:) y        -- ^ Inequality of Terms

pApp x args = PredApp x args            -- ^ Predicate symbol application to terms

-- * Term builders

var = Var                               -- ^ Variable
fApp x args = FunApp x args             -- ^ Function symbol application (constants are encoded as nullary functions)
numberLitTerm = NumberLitTerm           -- ^ Number literal
distinctObjectTerm = DistinctObjectTerm -- ^ Double-quoted string literal, called /Distinct Object/ in TPTP's grammar 

-- * Gathering free Variables
                              
class FreeVars a where
    -- | Obtain the free variables from a formula or term
    freeVars :: a -> Set V
             
instance FreeVars Formula where
    freeVars = foldF 
               freeVars   
               (\_ vars x -> S.difference (freeVars x) (S.fromList vars))                    
               (\x _ y -> (mappend `on` freeVars) x y)
               (\x _ y -> (mappend `on` freeVars) x y)
               (\_ args -> S.unions (fmap freeVars args))

instance FreeVars Term where
    freeVars = foldT
               (const mempty)
               (const mempty)
               S.singleton
               (\_ args -> S.unions (fmap freeVars args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: Formula -> Formula
univquant_free_vars cnf =
    if S.null free then cnf else for_all (S.toList free) cnf
    where free = freeVars cnf

-- * Utility functions

foldFormula ::
                  (Formula -> r)
                -> (Quant -> [V] -> Formula -> r)
                -> (Formula -> BinOp -> Formula -> r)
                -> (Term -> InfixPred -> Term -> r)
                -> (AtomicPredicate' -> [Term] -> r)
                -> Formula
                -> r
foldFormula kneg kquant kbinop kinfix kpredapp f =
    case f of
      (:~:) x -> kneg x
      Quant x y z -> kquant x y z
      BinOp x y z -> kbinop x y z
      InfixPred x y z -> kinfix x y z
      PredApp x y -> kpredapp x y
                      
foldTerm ::
               (String -> r)
             -> (Double -> r)
             -> (V -> r)
             -> (AtomicFunction' -> [Term] -> r)
             -> Term
             -> r
foldTerm kdistinct knum kvar kfunapp t =
    case t of
      DistinctObjectTerm x -> kdistinct x
      NumberLitTerm x -> knum x
      Var x -> kvar x
      FunApp x y -> kfunapp x y


-- | Eliminate formulae
foldF ::
           (Formula -> r) -- ^ Handle negation
         -> (Quant -> [V] -> Formula -> r) -- ^ Handle quantification
         -> (Formula -> BinOp -> Formula -> r) -- ^ Handle binary op
         -> (Term -> InfixPred -> Term -> r) -- ^ Handle equality/inequality
         -> (AtomicPredicate' -> [Term] -> r) -- ^ Handle predicate symbol application
         -> (Formula -> r) -- ^ Handle formula
         
foldF kneg kquant kbinop kinfix kpredapp f = foldFormula kneg kquant kbinop kinfix kpredapp (unwrapF f)

-- | Eliminate terms
foldT ::
           (String -> r) -- ^ Handle string literal
         -> (Double -> r) -- ^ Handle number literal
         -> (V -> r) -- ^ Handle variable
         -> (AtomicFunction' -> [Term] -> r) -- ^ Handle function symbol application
         -> (Term -> r) -- ^ Handle term
foldT kdistinct knum kvar kfunapp t = foldTerm kdistinct knum kvar kfunapp (unwrapT t)

unwrapF = id
unwrapT = id

-- * Substituting variables

-- |Helper function for variable substitution.  Each pair in the list
-- is a variable to be replaced and a formula in which it is free.
-- Substitute the single new variable into all of the formulas where
-- the old ones were.
substitute' :: V -> V -> Formula -> Formula
substitute' new old f = 
    sf f
    where
      sf :: Formula -> Formula
      sf ((:~:) f') = (:~:) (sf f')
      sf (Quant q vs f') = Quant q (map (\ v -> if v == old then new else v) vs) (sf f')
      sf (BinOp f1 op f2) = BinOp (sf f1) op (sf f2)
      sf (InfixPred t1 op t2) = InfixPred (st t1) op (st t2)
      sf (PredApp a ts) = PredApp a (map st ts)

      st :: Term -> Term
      st (Var v) = Var (if v == old then new else v)
      st (FunApp w ts) = FunApp w (map st ts)
      st (NumberLitTerm s) = NumberLitTerm s
      st (DistinctObjectTerm s) = DistinctObjectTerm s

-- |Substitute V for the (single) free variable in the formula.
substitute :: V -> Formula -> Formula
substitute new f =
    case S.toList (freeVars f) of
      [old] -> substitute' new old f
      _ -> error "subtitute: formula must have exactly one free variable"

instance Version Term
instance Version InfixPred
instance Version BinOp
instance Version V
instance Version Quant
instance Version Formula

$(deriveSerialize ''Term)
$(deriveSerialize ''InfixPred)
$(deriveSerialize ''BinOp)
$(deriveSerialize ''V)
$(deriveSerialize ''Quant)
$(deriveSerialize ''Formula)

$(deriveNewData [''Term, ''InfixPred, ''BinOp, ''V, ''Quant, ''Formula])
