{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
-- |Data types which are instances of the Logic type class for use
-- when you just want to use the classes and you don't have a
-- particular representation you need to use.
module Data.Logic.Types.FirstOrder
    ( Formula(..)
    , PTerm(..)
    ) where

import Data.Data (Data)
import Data.Logic.Classes.Arity (Arity)
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), showFirstOrder, Quant(..), Predicate(..), Pred(..), pApp)
import Data.Logic.Classes.Literal (Literal(..), PredicateLit(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..), showTerm)
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Typeable (Typeable)
import Happstack.Data (deriveNewData)

-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = Predicate (Predicate p (PTerm v f))
    | Combine (Combination (Formula v p f))
    | Quant Quant v (Formula v p f)
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq,Ord,Data,Typeable)

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
    show = showFirstOrder

instance (FirstOrderFormula (Formula v p f) (PTerm v f) v p f, Show v, Show p, Show f) => Show (PTerm v f) where
    show = showTerm

instance Negatable (Formula v p f) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False

instance (Constants p, Arity p, Ord p, Ord v, Ord f) => Constants (Formula v p f) where
    fromBool x = pApp0 (fromBool x)

instance (Constants (Formula v p f), Ord v, Ord p, Ord f) => Combinable (Formula v p f) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance (Ord v, Variable v, Data v,
          Ord p, Constants p, Arity p, Data p,
          Ord f, Skolem f, Data f,
          Constants (Formula v p f), Combinable (Formula v p f)) =>
         PropositionalFormula (Formula v p f) (Formula v p f) where
    atomic (Predicate (Equal t1 t2)) = t1 .=. t2
    atomic (Predicate (NotEqual t1 t2)) = t1 .!=. t2
    atomic (Predicate (Apply p ts)) = pApp p ts
    atomic _ = error "atomic method of PropositionalFormula for Parameterized: invalid argument"
    foldPropositional c a formula =
        case formula of
          Quant _ _ _ -> error "foldF0: quantifiers should not be present"
          Combine x -> c x
          Predicate x -> a (Predicate x)

instance (Ord v, Variable v, Data v, Eq f, Ord f, Skolem f, Data f) => Term (PTerm v f) v f where
    foldTerm vf fn t =
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

instance (Constants (Formula v p f), Ord v, Ord p, Constants p, Arity p, Ord f) => Pred p (PTerm v f) (Formula v p f) where
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

instance (Pred p (PTerm v f) (Formula v p f),
          Variable v, Ord v, Data v, Show v,
          Ord p, Data p, Show p,
          Skolem f, Ord f, Data f, Show f) =>
         FirstOrderFormula (Formula v p f) (PTerm v f) v p f where
    for_all v x = Quant All v x
    exists v x = Quant Exists v x
    foldFirstOrder q c p f =
        case f of
          Quant op v f' -> q op v f'
          Combine x -> c x
          Predicate x -> p x
    zipFirstOrder q c p f1 f2 =
        case (f1, f2) of
          (Quant q1 v1 f1', Quant q2 v2 f2') -> q q1 v1 (Quant q1 v1 f1') q2 v2 (Quant q2 v2 f2')
          (Combine x, Combine y) -> c x y
          (Predicate x, Predicate y) -> p x y
          _ -> Nothing

instance (Constants (Formula v p f),
          Variable v, Ord v, Data v, Show v,
          Arity p, Constants p, Ord p, Data p, Show p,
          Skolem f, Ord f, Data f, Show f) => Literal (Formula v p f) (PTerm v f) v p f where
    equals x y = Predicate (Equal x y)
    pAppLiteral p ts = Predicate (Apply p ts)
    foldLiteral c pr l =
        case l of
          (Combine ((:~:) x)) -> c x
          (Predicate (Apply p ts)) -> pr (ApplyLit p ts)
          (Predicate (Equal x y)) -> pr (EqualLit x y)
          _ -> error "Invalid formula used as Literal instance"
    zipLiterals c pr l1 l2 =
        case (l1, l2) of
          (Combine ((:~:) x), Combine ((:~:) y)) -> c x y
          (Predicate (Apply p1 ts1), Predicate (Apply p2 ts2)) -> pr (ApplyLit p1 ts1) (ApplyLit p2 ts2)
          _ -> Nothing

$(deriveSafeCopy 1 'base ''PTerm)
$(deriveSafeCopy 1 'base ''Formula)

$(deriveNewData [''PTerm, ''Formula])
