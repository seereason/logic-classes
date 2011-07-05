{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
-- |Data types which are instances of the Logic type class for use
-- when you just want to use the classes and you don't have a
-- particular representation you need to use.
module Logic.Instances.Native
    ( Formula(..)
    , PTerm(..)
    ) where

import Data.Data (Data)
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Logic.FirstOrder (Term(..), FirstOrderFormula(..), Quant(..), Skolem(..), Variable,
                         Pretty, Predicate(..), showForm, showTerm, Arity, pApp)
import Logic.Logic (Negatable(..), Logic(..), BinOp(..), Boolean(..), Combine(..))
import qualified Logic.Logic as Logic
import Logic.Propositional (PropositionalFormula(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = Predicate (Predicate p (PTerm v f))
    | Combine (Combine (Formula v p f))
    | Quant Quant v (Formula v p f) 
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Read,Data,Typeable)

-- | The range of a term is an element of a set.
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Read,Data,Typeable)

-- data InfixPred = (:=:) | (:!=:) deriving (Eq,Ord,Show,Data,Typeable,Enum,Bounded)

-- |We need to implement read manually here due to
-- <http://hackage.haskell.org/trac/ghc/ticket/4136>
{-
instance Read InfixPred where
    readsPrec _ s = 
        map (\ (x, t) -> (x, drop (length t) s))
            (take 1 (dropWhile (\ (_, t) -> not (isPrefixOf t s)) prs))
        where
          prs = [((:=:), ":=:"),
                 ((:!=:), ":!=:")]
-}

instance (FirstOrderFormula (Formula v p f) (PTerm v f) v p f, Show v, Show p, Show f) => Show (Formula v p f) where
    show = showForm

instance (FirstOrderFormula (Formula v p f) (PTerm v f) v p f, Show v, Show p, Show f) => Show (PTerm v f) where
    show = showTerm

instance Negatable (Formula v p f) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False
    
instance Logic (Formula v p f) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance (Ord v, Variable v, Data v, Pretty v, Show v,
          Ord p, Boolean p, Arity p, Data p, Pretty p, Show p,
          Ord f, Skolem f, Data f, Pretty f, Show f,
          Logic (Formula v p f), Show (Formula v p f)) =>
         PropositionalFormula (Formula v p f) (Formula v p f) where
    atomic (Predicate (Equal t1 t2)) = t1 .=. t2
    atomic (Predicate (NotEqual t1 t2)) = t1 .!=. t2
    atomic (Predicate (Apply p ts)) = pApp p ts
    atomic _ = error "atomic method of PropositionalFormula for Parameterized: invalid argument"
    foldF0 c a formula =
        case formula of
          Quant _ _ _ -> error "foldF0: quantifiers should not be present"
          Combine x -> c x
          Predicate x -> a (Predicate x)

instance (Ord v, Variable v, Data v, Pretty v, Eq f, Ord f, Skolem f, Data f, Pretty f) => Term (PTerm v f) v f where
    foldT vf fn t =
        case t of
          Var v -> vf v
          FunApp f ts -> fn f ts
    zipT v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FunApp f1 ts1, FunApp f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Var
    fApp x args = FunApp x args

instance (Ord v, Variable v, Data v, Pretty v, Show v,
          Ord p, Boolean p, Arity p, Data p, Pretty p, Show p,
          Ord f, Skolem f, Data f, Pretty f, Show f,
          Show (Formula v p f),
          PropositionalFormula (Formula v p f) (Formula v p f), Term (PTerm v f) v f) =>
          FirstOrderFormula (Formula v p f) (PTerm v f) v p f where
    for_all v x = Quant All v x
    exists v x = Quant Exists v x
    foldF q c p f =
        case f of
          -- Be careful not to create quants with empty variable lists
          Quant op v f' -> q op v f'
          Combine x -> c x
          Predicate x -> p x
    zipF q c p f1 f2 =
        case (f1, f2) of
          (Quant q1 v1 f1', Quant q2 v2 f2') -> q q1 v1 (Quant q1 v1 f1') q2 v2 (Quant q2 v2 f2')
          (Combine x, Combine y) -> c x y
          (Predicate x, Predicate y) -> p x y
          _ -> Nothing
    pApp0 x = Predicate (Apply x [])
    pApp1 x a = Predicate (Apply x [a])
    pApp2 x a b = Predicate (Apply x [a,b])
    pApp3 x a b c = Predicate (Apply x [a,b,c])
    pApp4 x a b c d = Predicate (Apply x [a,b,c,d])
    pApp5 x a b c d e = Predicate (Apply x [a,b,c,d,e])
    pApp6 x a b c d e f = Predicate (Apply x [a,b,c,d,e,f])
    pApp7 x a b c d e f g = Predicate (Apply x [a,b,c,d,e,f,g])
    x .=. y = Predicate (Equal x y)
    x .!=. y = Predicate (NotEqual x y)

$(deriveSafeCopy 1 'base ''PTerm)
$(deriveSafeCopy 1 'base ''Formula)

$(deriveNewData [''PTerm, ''Formula])
