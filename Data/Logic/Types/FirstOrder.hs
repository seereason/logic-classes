{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Data.Logic.Types.FirstOrder
    ( withUnivQuants
    , NFormula(..)
    , NTerm(..)
    , NPredicate(..)
    ) where

import Data.Data (Data)
import Data.SafeCopy (base, deriveSafeCopy)
import Data.String (IsString(fromString))
import Data.Typeable (Typeable)
import Formulas (IsAtom, IsFormula(..))
import Quantified (associativityQuantified, exists, IsQuantified(..), precedenceQuantified, prettyQuantified, Quant(..))
import Equate (associativityEquate, HasEquate(equate, foldEquate), overtermsEq, ontermsEq, precedenceEquate, prettyEquate)
import Apply (HasApply(..), IsPredicate, prettyApply)
import Term (IsFunction, IsTerm(..), IsVariable(..), prettyTerm, V)
import FOL (IsFirstOrder)
import Lit (IsLiteral(..))
import Pretty (HasFixity(..), Pretty(pPrint, pPrintPrec), Side(Top))
import Prop (BinOp(..), IsPropositional(..))

-- | Examine the formula to find the list of outermost universally
-- quantified variables, and call a function with that list and the
-- formula after the quantifiers are removed.
withUnivQuants :: IsQuantified formula => ([VarOf formula] -> formula -> r) -> formula -> r
withUnivQuants fn formula =
    doFormula [] formula
    where
      doFormula vs f =
          foldQuantified
                (doQuant vs)
                (\ _ _ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                f
      doQuant vs (:!:) v f = doFormula (v : vs) f
      doQuant vs (:?:) v f = fn (reverse vs) (exists v f)

-- | The range of a formula is {True, False} when it has no free variables.
data NFormula v p f
    = Predicate (NPredicate p (NTerm v f))
    | Combine (NFormula v p f) BinOp (NFormula v p f)
    | Negate (NFormula v p f)
    | Quant Quant v (NFormula v p f)
    | TT
    | FF
    -- Note that a derived Eq instance is not going to tell us that
    -- a&b is equal to b&a, let alone that ~(a&b) equals (~a)|(~b).
    deriving (Eq, Ord, Data, Typeable, Show)

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldFirstOrder and makes it easier to manage the
-- mapping of the different instances to the class methods.
data NPredicate p term
    = Equal term term
    | Apply p [term]
    deriving (Eq, Ord, Data, Typeable, Show)

-- | The range of a term is an element of a set.
data NTerm v f
    = NVar v                        -- ^ A variable, either free or
                                    -- bound by an enclosing quantifier.
    | FunApp f [NTerm v f]           -- ^ Function application.
                                    -- Constants are encoded as
                                    -- nullary functions.  The result
                                    -- is another term.
    deriving (Eq, Ord, Data, Typeable, Show)

instance IsVariable v => IsString (NTerm v f) where
    fromString = NVar . fromString
instance (IsVariable v, Pretty v, IsFunction f, Pretty f) => Pretty (NTerm v f) where
    pPrintPrec = prettyTerm
instance (IsPredicate p, IsTerm term) => HasFixity (NPredicate p term) where
    precedence = precedenceEquate
    associativity = associativityEquate
instance (IsPredicate p, IsTerm term) => IsAtom (NPredicate p term)
instance HasFixity (NTerm v f) where

instance (IsVariable v, IsPredicate p, IsFunction f, atom ~ NPredicate p (NTerm v f), Pretty atom
         ) => IsPropositional (NFormula v p f) where
    foldPropositional' ho _ _ _ _ fm@(Quant _ _ _) = ho fm
    foldPropositional' _ co _ _ _ (Combine x op y) = co x op y
    foldPropositional' _ _ ne _ _ (Negate x) = ne x
    foldPropositional' _ _ _ tf _ TT = tf True
    foldPropositional' _ _ _ tf _ FF = tf False
    foldPropositional' _ _ _ _ at (Predicate x) = at x
    a .|. b = Combine a (:|:) b
    a .&. b = Combine a (:&:) b
    a .=>. b = Combine a (:=>:) b
    a .<=>. b = Combine a (:<=>:) b
    foldCombination = error "FIXME foldCombination"
instance (IsVariable v, IsPredicate p, IsFunction f) => HasFixity (NFormula v p f) where
    precedence = precedenceQuantified
    associativity = associativityQuantified
--instance (IsVariable v, IsPredicate p, IsFunction f) => Pretty (NPredicate p (NTerm v f)) where
--    pPrint p = foldEquate prettyEquate prettyApply p
instance (IsPredicate p, IsTerm term) => Pretty (NPredicate p term) where
    pPrintPrec d r = foldEquate (prettyEquate d r) prettyApply
instance (IsVariable v, IsPredicate p, IsFunction f) => Pretty (NFormula v p f) where
    pPrintPrec = prettyQuantified Top
instance (IsPredicate p, IsTerm term) => HasApply (NPredicate p term) where
    type PredOf (NPredicate p term) = p
    type TermOf (NPredicate p term) = term
    applyPredicate = Apply
    foldApply' _ f (Apply p ts) = f p ts
    foldApply' d _ x = d x
    overterms = overtermsEq
    onterms = ontermsEq
instance (IsPredicate p, IsTerm term) => HasEquate (NPredicate p term) where
    equate = Equal
    foldEquate eq _ (Equal t1 t2) = eq t1 t2
    foldEquate _ ap (Apply p ts) = ap p ts
{-
instance HasBoolean p => HasBoolean (NPredicate p (NTerm v f)) where
    fromBool x = Apply (fromBool x) []
    asBool (Apply p []) = asBool p
    asBool _ = Nothing
-}
instance (IsVariable v, IsPredicate p, IsFunction f
         ) => IsFormula (NFormula v p f) where
    type AtomOf (NFormula v p f) = NPredicate p (NTerm v f)
    atomic = Predicate
    onatoms f (Negate fm) = Negate (onatoms f fm)
    onatoms _ TT = TT
    onatoms _ FF = FF
    onatoms f (Combine lhs op rhs) = Combine (onatoms f lhs) op (onatoms f rhs)
    onatoms f (Quant op v fm) = Quant op v (onatoms f fm)
    onatoms f (Predicate p) = Predicate (f p)
    overatoms f (Negate fm) b = overatoms f fm b
    overatoms _ TT b = b
    overatoms _ FF b = b
    overatoms f (Combine lhs _ rhs) b = overatoms f lhs (overatoms f rhs b)
    overatoms f (Quant _ _ fm) b = overatoms f fm b
    overatoms f (Predicate p) b = f p b
    asBool TT = Just True
    asBool FF = Just False
    asBool _ = Nothing
    true = TT
    false = FF
instance (IsVariable v, IsPredicate p, IsFunction f
         , atom ~ NPredicate p (NTerm v f) -- , Pretty atom
         ) => IsQuantified (NFormula v p f) where
    type VarOf (NFormula v p f) = v
    foldQuantified qu _ _ _ _ (Quant op v fm) = qu op v fm
    foldQuantified _ co ne tf at fm = foldPropositional' (error "FIXME - need other function in case of embedded quantifiers") co ne tf at fm
    quant = Quant
instance (IsVariable v, IsPredicate p, IsFunction f
         , atom ~ NPredicate p (NTerm v f) -- , Pretty atom
         ) => IsLiteral (NFormula v p f) where
    foldLiteral' ho ne _tf at fm =
        case fm of
          Negate fm' -> ne fm'
          Predicate x -> at x
          _ -> ho fm
    naiveNegate = Negate
    foldNegation _ ne (Negate x) = ne x
    foldNegation other _ fm = other fm
{-
instance (IsPredicate p, IsVariable v, IsFunction f, IsAtom (NPredicate p (NTerm v f))
         ) => HasEquate (NPredicate p (NTerm v f)) p (NTerm v f) where
    overterms = overtermsEq
    onterms = ontermsEq
-}
instance (IsVariable v, IsPredicate p, IsFunction f, IsAtom (NPredicate p (NTerm v f))
         ) => IsFirstOrder (NFormula v p f)

instance (IsVariable v, IsFunction f) => IsTerm (NTerm v f) where
    type TVarOf (NTerm v f) = v
    type FunOf (NTerm v f) = f
    vt = NVar
    fApp = FunApp
    foldTerm vf _ (NVar v) = vf v
    foldTerm _ ff (FunApp f ts) = ff f ts

$(deriveSafeCopy 1 'base ''BinOp)
$(deriveSafeCopy 1 'base ''Quant)
$(deriveSafeCopy 1 'base ''NFormula)
$(deriveSafeCopy 1 'base ''NPredicate)
$(deriveSafeCopy 1 'base ''NTerm)
$(deriveSafeCopy 1 'base ''V)
