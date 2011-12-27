{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS -fno-warn-missing-signatures -fno-warn-orphans #-}
-- |Data types which are instances of the Logic type class for use
-- when you just want to use the classes and you don't have a
-- particular representation you need to use.
module Data.Logic.Types.FirstOrder
    ( Formula(..)
    , PTerm(..)
    , Predicate(..)
    ) where

import Data.Data (Data)
import Data.Logic.Classes.Arity (Arity)
-- import Data.Logic.Classes.Atom (Atom(..))
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..), asBool)
import Data.Logic.Classes.Equals (AtomEq(..), (.=.), (.!=.), pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Classes.Variable (Variable(..))
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
    deriving (Eq,Ord,Data,Typeable,Show)

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldFirstOrder and makes it easier to manage the
-- mapping of the different instances to the class methods.
data Predicate p term
    = Equal term term
    | NotEqual term term
    | Constant Bool
    | Apply p [term]
    deriving (Eq,Ord,Data,Typeable,Show,Read)

-- | The range of a term is an element of a set.
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq,Ord,Data,Typeable,Show,Read)

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
{-
instance (FirstOrderFormula (Formula v p f) (Predicate p (PTerm v f)) v, Show v, Show p, Show f, Arity p, Skolem f, Data v, Data f, Constants p, Ord f) => Show (Formula v p f) where
    show = showFirstOrderEq

instance (FirstOrderFormula (Formula v p f) (Predicate p (PTerm v f)) v, Show v, Show p, Show f, Skolem f, Data v, Data f, Ord f) => Show (PTerm v f) where
    show = showTerm
-}
instance Negatable (Formula v p f) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False

instance Constants p => Constants (Formula v p f) where
    fromBool x = Predicate (Apply (fromBool x) [])

{-
instance (Constants p, Arity p, Ord p, Ord v, Ord f, Variable v, Skolem f, Show p, Show v, Show f, Data f, Data v, Data p) => Constants (Formula v p f) where
    fromBool x = pApp0 (fromBool x)
-}

instance (Constants (Formula v p f), Ord v, Ord p, Ord f) => Combinable (Formula v p f) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance (Ord v, Variable v, Data v, Show v,
          Ord p, Constants p, Arity p, Data p, Show p,
          Ord f, Skolem f, Data f, Show f,
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

instance (Variable v, Data v, Skolem f, Data f, Ord f) => Term (PTerm v f) v f where
    foldTerm vf fn t =
        case t of
          Var v -> vf v
          FunApp f ts -> fn f ts
    zipTerms v f t1 t2 =
        case (t1, t2) of
          (Var v1, Var v2) -> v v1 v2
          (FunApp f1 ts1, FunApp f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    vt = Var
    fApp x args = FunApp x args

{-
instance (Arity p, Constants p) => Atom (Predicate p (PTerm v f)) p (PTerm v f) where
    foldAtom ap (Apply p ts) = ap p ts
    foldAtom ap (Constant x) = ap (fromBool x) []
    foldAtom _ _ = error "foldAtom Predicate"
    zipAtoms ap (Apply p1 ts1) (Apply p2 ts2) = ap p1 ts1 p2 ts2
    zipAtoms ap (Constant x) (Constant y) = ap (fromBool x) [] (fromBool y) []
    zipAtoms _ _ _ = error "zipAtoms Predicate"
    apply' = Apply
-}

instance (Constants p, Eq p, Arity p, Show p) => AtomEq (Predicate p (PTerm v f)) p (PTerm v f) where
    foldAtomEq ap tf _ (Apply p ts) = maybe (ap p ts) tf (asBool p)
    -- foldAtomEq ap _ _ (Constant x) = ap (fromBool x) []
    foldAtomEq _ _ eq (Equal t1 t2) = eq t1 t2
    foldAtomEq _ _ _ _ = error "foldAtomEq Predicate"
    zipAtomsEq ap tf _ (Apply p1 ts1) (Apply p2 ts2) =
        case (asBool p1, asBool p2) of
          (Just a, Just b) -> tf a b
          (Nothing, Nothing) -> ap p1 ts1 p2 ts2
          _ -> Nothing
    -- zipAtomsEq ap _ (Constant x) (Constant y) = ap (fromBool x) [] (fromBool y) []
    zipAtomsEq _ _ eq (Equal t1 t2) (Equal t3 t4) = eq t1 t2 t3 t4
    zipAtomsEq _ _ _ _ _ = Nothing
    equals = Equal
    applyEq' = Apply

instance (AtomEq (Predicate p (PTerm v f)) p (PTerm v f),
          Constants (Formula v p f),
          Variable v, Ord v, Data v, Show v,
          Ord p, Data p, Show p, Constants p,
          Skolem f, Ord f, Data f, Show f) =>
         FirstOrderFormula (Formula v p f) (Predicate p (PTerm v f)) v where
    for_all v x = Quant Forall v x
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
    atomic = Predicate

instance (Constants (Formula v p f),
          Variable v, Ord v, Data v, Show v,
          Arity p, Constants p, Ord p, Data p, Show p,
          Skolem f, Ord f, Data f, Show f) => Literal (Formula v p f) (Predicate p (PTerm v f)) v where
    foldLiteral c pr l =
        case l of
          (Combine ((:~:) x)) -> c x
          (Predicate p) -> pr p
          _ -> error "Literal (Formula v p f)"
    zipLiterals c pr l1 l2 =
        case (l1, l2) of
          (Combine ((:~:) x), Combine ((:~:) y)) -> c x y
          (Predicate p1, Predicate p2) -> pr p1 p2
          _ -> Nothing
    atomic = Predicate

$(deriveSafeCopy 1 'base ''PTerm)
$(deriveSafeCopy 1 'base ''Formula)
$(deriveSafeCopy 1 'base ''Predicate)

$(deriveNewData [''PTerm, ''Formula, ''Predicate])
