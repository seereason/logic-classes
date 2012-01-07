{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
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
import Data.Logic.Classes.Combine (Combinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (Constants(..), asBool)
import Data.Logic.Classes.Equals (AtomEq(..), (.=.), pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate (Negatable(..))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Classes.Variable (Variable(..))
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.SafeCopy (SafeCopy, base, deriveSafeCopy, extension, MigrateFrom(..))
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

instance Negatable (Formula v p f) where
    (.~.) (Combine ((:~:) (Combine ((:~:) x)))) = (.~.) x
    (.~.) (Combine ((:~:) x)) = x
    (.~.) x = Combine ((:~:) x)
    negated (Combine ((:~:) x)) = not (negated x)
    negated _ = False

instance Constants p => Constants (Formula v p f) where
    fromBool = Predicate . fromBool

instance Constants p => Constants (Predicate p (PTerm v f)) where
    fromBool x = Apply (fromBool x) []

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
    atomic (Predicate (Apply p ts)) = pApp p ts
    atomic _ = error "atomic method of PropositionalFormula for Parameterized: invalid argument"
    foldPropositional co tf at formula =
        maybe testFm tf (asBool formula)
        where
          testFm =
              case formula of
                Quant _ _ _ -> error "foldF0: quantifiers should not be present"
                Combine x -> co x
                Predicate x -> at (Predicate x)

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
    foldAtomEq _ _ eq (Equal t1 t2) = eq t1 t2
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
    foldFirstOrder qu co tf at f =
        maybe testFm tf (asBool f)
            where testFm = case f of
                             Quant op v f' -> qu op v f'
                             Combine x -> co x
                             Predicate x -> at x
{-
    zipFirstOrder qu co tf at f1 f2 =
        case (f1, f2) of
          (Quant q1 v1 f1', Quant q2 v2 f2') -> qu q1 v1 (Quant q1 v1 f1') q2 v2 (Quant q2 v2 f2')
          (Combine x, Combine y) -> co x y
          (Predicate x, Predicate y) -> at x y
          _ -> Nothing
-}
    atomic = Predicate

{-
instance (Constants (Formula v p f),
          Variable v, Ord v, Data v, Show v,
          Arity p, Constants p, Ord p, Data p, Show p,
          Skolem f, Ord f, Data f, Show f) => Literal (Formula v p f) (Predicate p (PTerm v f)) v where
    foldLiteral co tf at l =
        case l of
          (Combine ((:~:) x)) -> co x
          (Predicate p) -> at p
          _ -> error "Literal (Formula v p f)"
    atomic = Predicate
-}

instance (Constants p, Eq v, Eq p, Eq f, Constants (Predicate p (PTerm v f))) => Literal (Formula v p f) (Predicate p (PTerm v f)) v where
    atomic = Predicate
    foldLiteral neg tf at f =
        case f of
          Quant _ _ _ -> error "Invalid literal"
          Combine ((:~:) p) -> neg p
          Combine _ -> error "Invalid literal"
          Predicate p -> if p == fromBool True
                         then tf True
                         else if p == fromBool False
                              then tf False
                              else at p

$(deriveSafeCopy 1 'base ''PTerm)
$(deriveSafeCopy 1 'base ''Formula)
$(deriveSafeCopy 2 'extension ''Predicate)

$(deriveNewData [''PTerm, ''Formula, ''Predicate])

-- Migration --

data Predicate_v1 p term
    = Equal_v1 term term
    | NotEqual_v1 term term
    | Constant_v1 Bool
    | Apply_v1 p [term]
    deriving (Eq,Ord,Data,Typeable,Show,Read)

$(deriveSafeCopy 1 'base ''Predicate_v1)

instance (SafeCopy p, SafeCopy term) => Migrate (Predicate p term) where
    type MigrateFrom (Predicate p term) = (Predicate_v1 p term)
    migrate (Equal_v1 t1 t2) = Equal t1 t2
    migrate (Apply_v1 p ts) = Apply p ts
    migrate (NotEqual_v1 _ _) = error "Failure migrating Predicate NotEqual"
    migrate (Constant_v1 _) = error "Failure migrating Predicate Constant"
