{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
-- |Data types which are instances of the Logic type class for use
-- when you just want to use the classes and you don't have a
-- particular representation you need to use.
module Logic.Instances.Native
    ( Formula(..)
    , PTerm(..)
    , ImplicativeNormalForm(..)
    , makeINF'
    ) where

import Data.Data (Data)
import qualified Data.Set as S
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)
import Happstack.State (Version, deriveSerialize)
import Logic.FirstOrder (Term(..), FirstOrderFormula(..), Quant(..), Skolem(..), Variable, Pretty, Predicate(..), showForm, showTerm)
import Logic.Logic (Negatable(..), Logic(..), BinOp(..), Boolean(..), Combine(..))
import qualified Logic.Logic as Logic
import Logic.Normal (ImplicativeNormalFormula(..))
import Logic.Propositional (PropositionalFormula(..))
    
-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = Quant Quant v (Formula v p f) 
    | Combine (Combine (Formula v p f))
    | Predicate (Predicate p (PTerm v f))
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

data (Ord v, Ord p, Ord f) => ImplicativeNormalForm v p f =
    INF (S.Set (Formula v p f)) (S.Set (Formula v p f))
    deriving (Eq, Ord, Data, Typeable)

instance (Ord v, Ord p, Ord f) => ImplicativeNormalFormula (ImplicativeNormalForm v p f) (Formula v p f) where
    neg (INF lhs _) = lhs
    pos (INF _ rhs) = rhs
    makeINF = INF

-- |A version of MakeINF that takes lists instead of sets, used for
-- implementing a more attractive show method.
makeINF' :: ImplicativeNormalFormula inf lit => [lit] -> [lit] -> inf
makeINF' n p = makeINF (S.fromList n) (S.fromList p)

instance (FirstOrderFormula (Formula v p f) (PTerm v f) v p f, Show (Formula v p f)) => Show (ImplicativeNormalForm v p f) where
    show x = "makeINF' (" ++ show (S.toList (neg x)) ++ ") (" ++ show (S.toList (pos x)) ++ ")"

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
          Ord p, Boolean p, Data p, Pretty p, Show p,
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

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f) => Term (PTerm v f) v f where
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
          Ord p, Boolean p, Data p, Pretty p, Show p,
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
    pApp x args = Predicate (Apply x args)
    x .=. y = Predicate (Equal x y)
    x .!=. y = Predicate (NotEqual x y)

instance Version (PTerm v f)
instance Version (Formula v p f)

$(deriveSerialize ''PTerm)
$(deriveSerialize ''Formula)

$(deriveNewData [''PTerm, ''Formula])
