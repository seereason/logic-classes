{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
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
import Data.List (intercalate)
import Data.Logic.Classes.Apply as C
import qualified Data.Logic.Classes.Atom as C
import Data.Logic.Classes.Combine (IsCombinable(..), Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (HasBoolean(..), asBool)
import Data.Logic.Classes.Equals (HasEquals, HasEquality(..), substAtomEq, varAtomEq, prettyAtomEq)
import Data.Logic.Classes.FirstOrder (IsQuantified(..), Quant(..), prettyFirstOrder, fixityFirstOrder, overatomsFirstOrder, onatomsFirstOrder)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Literal (IsLiteral(..))
import Data.Logic.Classes.Negate (IsNegatable(..))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), leafFixity)
import Data.Logic.Classes.Term (IsTerm(..), Function, showTerm)
import Data.Logic.Classes.Variable (IsVariable(..))
import Data.Logic.Classes.Propositional (IsPropositional(..))
import Data.Logic.Harrison.Resolution (matchAtomsEq)
import Data.Logic.Harrison.Tableaux (unifyAtomsEq)
import Data.Logic.Resolution (isRenameOfAtomEq, getSubstAtomEq)
import Data.SafeCopy (SafeCopy, base, deriveSafeCopy, extension, MigrateFrom(..))
import Data.Typeable (Typeable)

-- | The range of a formula is {True, False} when it has no free variables.
data Formula v p f
    = Predicate (Predicate p (PTerm v f))
    | Combine (Combination (Formula v p f))
    | Quant Quant v (Formula v p f)
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq, Ord, Data, Typeable)

instance (Show v, Show p, Show f, Function f v) => Show (Formula v p f) where
    show (Predicate p) = show p
    show (Combine c) = error "show c"
    show (Quant q v f) = show q ++ " " ++ show v ++ " (" ++ show f ++ ")"

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldFirstOrder and makes it easier to manage the
-- mapping of the different instances to the class methods.
data Predicate p term
    = Equal term term
    | Apply p [term]
    deriving (Eq, Ord, Data, Typeable)

instance (Show p, Show term) => Show (Predicate p term) where
    show (Equal a b) = show a ++ " .=. " ++ show b
    show (Apply p ts) = "pApp " ++ show p ++ " [" ++ intercalate ", " (map show ts) ++ "]"

-- | The range of a term is an element of a set.
data PTerm v f
    = Var v                         -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [PTerm v f]           -- ^ Function application.
                                    -- HasBoolean are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq, Ord, Data, Typeable)

instance (Show v, Show f, Function f v) => Show (PTerm v f) where
    show = showTerm

instance (Data p, Data v, Data f, Ord p, Ord v, Ord f) => IsNegatable (Formula v p f) where
    naiveNegate x = Combine ((:~:) x)
    foldNegation normal inverted (Combine ((:~:) x)) = foldNegation inverted normal x
    foldNegation normal _ x = normal x

instance (HasBoolean p, Data p, Data v, Data f, Ord p, Ord v, Ord f) => HasBoolean (Formula v p f) where
    fromBool = Predicate . fromBool
    asBool (Predicate x) = asBool x
    asBool _ = Nothing

instance (Data p, HasBoolean p, Data v, Data f, Ord p, Ord v, Ord f) => HasBoolean (Predicate p (PTerm v f)) where
    fromBool x = Apply (fromBool x) []
    asBool (Apply p _) = asBool p
    asBool _ = Nothing

instance (HasBoolean (Formula v p f), Data p, Data v, Data f, Ord p, Ord v, Ord f) => IsCombinable (Formula v p f) where
    x .<=>. y = Combine (BinOp  x (:<=>:) y)
    x .=>.  y = Combine (BinOp  x (:=>:)  y)
    x .|.   y = Combine (BinOp  x (:|:)   y)
    x .&.   y = Combine (BinOp  x (:&:)   y)

instance (HasEquals p, C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), Function f v) => C.IsFormula (Formula v p f) (Predicate p (PTerm v f)) where
    atomic = Predicate
    overatoms = overatomsFirstOrder
    onatoms = onatomsFirstOrder

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), C.IsFormula (Formula v p f) (Predicate p (PTerm v f)), IsVariable v, HasEquals p, Function f v, HasBoolean (Formula v p f), IsCombinable (Formula v p f)
         ) => IsPropositional (Formula v p f) (Predicate p (PTerm v f)) where
    foldPropositional co tf at formula =
        maybe testFm tf (asBool formula)
        where
          testFm =
              case formula of
                Quant _ _ _ -> error "foldF0: quantifiers should not be present"
                Combine x -> co x
                Predicate x -> at x

instance (IsVariable v, Function f v) => IsTerm (PTerm v f) v f where
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
instance (Arity p, HasBoolean p) => Atom (Predicate p (PTerm v f)) p (PTerm v f) where
    foldAtom ap (Apply p ts) = ap p ts
    foldAtom ap (Constant x) = ap (fromBool x) []
    foldAtom _ _ = error "foldAtom Predicate"
    zipAtoms ap (Apply p1 ts1) (Apply p2 ts2) = ap p1 ts1 p2 ts2
    zipAtoms ap (Constant x) (Constant y) = ap (fromBool x) [] (fromBool y) []
    zipAtoms _ _ _ = error "zipAtoms Predicate"
    apply' = Apply
-}

instance IsPredicate p => HasPredicate (Predicate p (PTerm v f)) p (PTerm v f) where
    foldPredicate ap (Apply p ts) = ap p ts
    foldPredicate _ap (Equal _lhs _rhs) = error "Attempt to use foldPredicate on Predicate.Equal"
    applyPredicate p ts = Apply p ts

{-
instance (p ~ AtomicPredicate description, term ~ PTerm v f, atom ~ Predicate p term,
            Data description, Ord description, Pretty description) => HasEquality atom p term where
    foldEquals f (Equal lhs rhs) = Just (f lhs rhs)
    foldEquals _ _ = Nothing
    applyEquals = Equal
-}

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), HasEquals p, Data v, Data f, Ord v, Ord f) => HasEquality (Predicate p (PTerm v f)) p (PTerm v f) where
    foldEquals ap (Equal t1 t2) = Just (ap t1 t2)
    foldEquals _ _ = Nothing
    -- foldAtomEq ap _ (Apply p ts) = ap p ts
    -- foldAtomEq _ eq (Equal t1 t2) = eq t1 t2
    applyEquals = Equal
    -- applyEq' = Apply

instance (C.IsFormula (Formula v p f) (Predicate p (PTerm v f)),
          HasEquality (Predicate p (PTerm v f)) p (PTerm v f),
          HasBoolean (Formula v p f),
          IsVariable v, C.IsPredicate p, Function f v
         ) => IsQuantified (Formula v p f) (Predicate p (PTerm v f)) v where
    quant = Quant
    foldQuantified qu co tf at f =
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

instance (HasBoolean (Formula v p f),
          IsVariable v, Ord v, Data v, Show v,
          Arity p, HasBoolean p, Ord p, Data p, Show p,
          Skolem f, Ord f, Data f, Show f) => IsLiteral (Formula v p f) (Predicate p (PTerm v f)) v where
    foldLiteral co tf at l =
        case l of
          (Combine ((:~:) x)) -> co x
          (Predicate p) -> at p
          _ -> error "IsLiteral (Formula v p f)"
    atomic = Predicate
-}

instance (HasBoolean p, Ord v, Ord p, Ord f, HasBoolean (Predicate p (PTerm v f)), C.IsFormula (Formula v p f) (Predicate p (PTerm v f)), Data p, Data v, Data f
         ) => IsLiteral (Formula v p f) (Predicate p (PTerm v f)) where
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

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), HasEquals p, IsVariable v, Function f v) => C.Atom (Predicate p (PTerm v f)) (PTerm v f) v where
    substitute = substAtomEq
    freeVariables = varAtomEq
    allVariables = varAtomEq
    unify = unifyAtomsEq
    match = matchAtomsEq
    foldTerms f r (Apply _ ts) = foldr f r ts
    foldTerms f r (Equal t1 t2) = f t2 (f t1 r)
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f),
          IsVariable v, Pretty v, HasEquals p, Pretty p,
          Function f v, Pretty f) => Pretty (Predicate p (PTerm v f)) where
    pPrint atom = prettyAtomEq pPrint pPrint pPrint 0 atom

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), C.IsFormula (Formula v p f) (Predicate p (PTerm v f)),
          HasEquals p, IsVariable v, Function f v, HasFixity (Predicate p (PTerm v f))) => HasFixity (Formula v p f) where
    fixity = fixityFirstOrder

instance (C.HasPredicate (Predicate p (PTerm v f)) p (PTerm v f), C.IsFormula (Formula v p f) (Predicate p (PTerm v f)), IsVariable v, HasEquals p, Function f v) => Pretty (Formula v p f) where
    pPrint f = prettyFirstOrder (\ _ -> pPrint) pPrint 0 $ f

instance HasFixity (Predicate p term) where
    fixity = const leafFixity

$(deriveSafeCopy 1 'base ''PTerm)
$(deriveSafeCopy 1 'base ''Formula)
$(deriveSafeCopy 2 'extension ''Predicate)

-- Migration --

data Predicate_v1 p term
    = Equal_v1 term term
    | NotEqual_v1 term term
    | Constant_v1 Bool
    | Apply_v1 p [term]
    deriving (Eq, Ord, Data, Typeable, Show, Read)

$(deriveSafeCopy 1 'base ''Predicate_v1)

instance (SafeCopy p, SafeCopy term) => Migrate (Predicate p term) where
    type MigrateFrom (Predicate p term) = (Predicate_v1 p term)
    migrate (Equal_v1 t1 t2) = Equal t1 t2
    migrate (Apply_v1 p ts) = Apply p ts
    migrate (NotEqual_v1 _ _) = error "Failure migrating Predicate NotEqual"
    migrate (Constant_v1 _) = error "Failure migrating Predicate Constant"
