{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- |An instance of the first order logic type class Formulae which is
-- parameterized on the atomic predicate and atomic function types.
-- It is patterned after Logic-TPTP, but without the wrappers and
-- with some constructors like :~&: omitted.
module Logic.Instances.Parameterized
    ( Formula(..)
    , Predicate
    , Proposition
    , Term(..)
    , V(..)
    ) where

import Data.Char (isDigit, ord, chr)
import Data.Data (Data)
import Data.Monoid (Monoid(..))
import Data.String (IsString)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.Logic (Logic(..), BinOp(..))
import Logic.Propositional (PropositionalLogic(..))
import Logic.Predicate (PredicateLogic(..), Quant(..), InfixPred(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula p f
    = PredApp p [Term f]                      -- ^ Predicate application.  The terms are the free variables.
    | (:~:) (Formula p f)                     -- ^ Negation
    | BinOp (Formula p f) BinOp (Formula p f) -- ^ Binary connective application
    | InfixPred (Term f) InfixPred (Term f)   -- ^ Infix predicate application (equalities, inequalities)
    | Quant Quant [V] (Formula p f)           -- ^ Quantified formula
    -- A derived Eq instance is not going to tell us that a&b
    -- is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

type Predicate = Formula
type Proposition = Formula

-- | The range of a term is an element of a set.
data Term f
    = Var V                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [Term f]             -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Show,Read,Data,Typeable)
                
-- | Variable names
newtype V = V String
    deriving (Eq,Ord,Data,Typeable,Read,Monoid,IsString)

instance Show V where
    show (V s) = show s

-- |Generate a series of variable names.  We *only* recognize variable
-- names which begin with one of the letters t thru z followed by zero
-- or more digits.
instance Enum V where
    succ v =
        toEnum (if n < cnt then n + 1 else if n == cnt then ord pref + cnt else n + cnt)
            where n = fromEnum v
    fromEnum (V s) =
        case break (not . isDigit) (reverse s) of
          ("", [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn
          (n, [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn + cnt * (read (reverse n) :: Int)
          _ -> error $ "Invalid variable name: " ++ show s
    toEnum n =
        V (chr (ord mn + pre) : if suf == 0 then "" else show suf)
        where (suf, pre) = divMod n cnt

mn = 'x'
pref = 'x'
mx = 'z'
cnt = ord mx - ord mn + 1

instance Logic (Formula p f) where
    x .<=>. y = BinOp  x (:<=>:) y
    x .=>.  y = BinOp  x (:=>:)  y
    x .|.   y = BinOp  x (:|:)   y
    x .&.   y = BinOp  x (:&:)   y
    (.~.) x   = (:~:) x

instance (Logic (Formula p f), Eq p, Eq f, Show p, Show f) =>
         PropositionalLogic (Formula p f) (Formula p f) where
    atomic (InfixPred t1 (:=:) t2) = t1 .=. t2
    atomic (InfixPred t1 (:!=:) t2) = t1 .!=. t2
    atomic (PredApp p ts) = pApp p ts
    atomic _ = error "atomic method of PropositionalLogic for Parameterized: invalid argument"
    foldF0 n b a formula =
        case formula of
          (:~:) x -> n x
          Quant _ _ _ -> error "foldF0: quantifiers should not be present"
          BinOp f1 op f2 -> b f1 op f2
          InfixPred t1 op t2 -> a (InfixPred t1 op t2)
          PredApp p ts -> a (PredApp p ts)

instance (PropositionalLogic (Formula p f) (Formula p f), Eq p, Eq f, Show p, Show f) =>
          PredicateLogic (Formula p f) (Term f) V p f where
    for_all vars x = Quant All vars x
    exists vars x = Quant Exists vars x
    foldF = foldFormula
    foldT = foldTerm
    pApp x args = PredApp x args
    var = Var
    fApp x args = FunApp x args
    x .=. y = InfixPred x (:=:) y
    x .!=. y = InfixPred x (:!=:) y

foldFormula ::
                  (Formula p f -> r)
               -> (Quant -> [V] -> Formula p f -> r)
               -> (Formula p f -> BinOp -> Formula p f -> r)
               -> (Term f -> InfixPred -> Term f -> r)
               -> (p -> [Term f] -> r)
               -> Formula p f
               -> r
foldFormula kneg kquant kbinop kinfix kpredapp f =
    case f of
      (:~:) x -> kneg x
      Quant x y z -> kquant x y z
      BinOp x y z -> kbinop x y z
      InfixPred x y z -> kinfix x y z
      PredApp x y -> kpredapp x y
                      
foldTerm ::
               (V -> r)
            -> (f -> [Term f] -> r)
            -> Term f
            -> r
foldTerm kvar kfunapp t =
    case t of
      Var x -> kvar x
      FunApp x y -> kfunapp x y

instance Version (Term f)
instance Version V
instance Version (Formula p f)

$(deriveSerialize ''Term)
$(deriveSerialize ''V)
$(deriveSerialize ''Formula)

$(deriveNewData [''Term, ''V, ''Formula])
