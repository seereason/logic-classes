{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Data.Logic.Types.FirstOrder
    ( withUnivQuants
    , NFormula(..)
    , NTerm(..)
    , NPredicate(..)
    ) where

import Data.Data (Data)
import Data.SafeCopy (base, deriveSafeCopy)
import Data.Typeable (Typeable)
import Formulas (Combination((:~:), BinOp), BinOp(..), IsNegatable(..), IsCombinable(..), HasBoolean(..), IsFormula(..))
import FOL (exists, HasEquals, HasEquate(equate, foldEquate'), HasFunctions(..), HasPredicate(..), IsFirstOrder,
            IsFunction, IsPredicate, IsQuantified(..), IsTerm(..), IsVariable(..),
            prettyPredicateApplicationEq, prettyQuantified, prettyTerm, Quant(..), V)
import Lit (IsLiteral(..))
import Pretty (HasFixity(..), Pretty(pPrint), prettyShow, rootFixity)
import Prop (IsPropositional(foldPropositional'))

-- | Examine the formula to find the list of outermost universally
-- quantified variables, and call a function with that list and the
-- formula after the quantifiers are removed.
withUnivQuants :: IsQuantified formula atom v => ([v] -> formula -> r) -> formula -> r
withUnivQuants fn formula =
    doFormula [] formula
    where
      doFormula vs f =
          foldQuantified
                (doQuant vs)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                f
      doQuant vs (:!:) v f = doFormula (v : vs) f
      doQuant vs (:?:) v f = fn (reverse vs) (exists v f)

-- | The range of a formula is {True, False} when it has no free variables.
data NFormula v p f
    = Predicate (NPredicate p (NTerm v f))
    | Combine (Combination (NFormula v p f))
    | Quant Quant v (NFormula v p f)
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

instance (IsVariable v, Pretty v, IsFunction f, Pretty f) => Pretty (NTerm v f) where
    pPrint = prettyTerm
instance (IsVariable v, IsPredicate p, IsFunction f
         ) => IsNegatable (NFormula v p f) where
    naiveNegate = Combine . (:~:)
    foldNegation' ne _ (Combine ((:~:) x)) = ne x
    foldNegation' _ other fm = other fm
instance (IsVariable v, IsPredicate p, IsFunction f
         ) => IsCombinable (NFormula v p f) where
    a .|. b = Combine (BinOp a (:|:) b)
    a .&. b = Combine (BinOp a (:&:) b)
    a .=>. b = Combine (BinOp a (:=>:) b)
    a .<=>. b = Combine (BinOp a (:<=>:) b)
    foldCombination = error "FIXME foldCombination"
instance (IsVariable v, IsPredicate p, HasBoolean p, IsFunction f, atom ~ NPredicate p (NTerm v f), Pretty atom
         ) => IsPropositional (NFormula v p f) atom where
    foldPropositional' ho _ _ _ fm@(Quant _ _ _) = ho fm
    foldPropositional' _ co _ _ (Combine x) = co x
    foldPropositional' _ _ tf at (Predicate x) = maybe (at x) tf (asBool x)
instance HasFixity (NFormula v p f) where
    fixity _ = rootFixity
instance (IsVariable v, IsPredicate p, IsFunction f, Pretty (NPredicate p (NTerm v f)), HasBoolean p) => Pretty (NFormula v p f) where
    pPrint = prettyQuantified
instance (IsPredicate p, Pretty p, Pretty term, HasEquals p, HasBoolean p) => Pretty (NPredicate p term) where
    pPrint = foldPredicate prettyPredicateApplicationEq
instance (IsPredicate p, HasBoolean p) => HasPredicate (NPredicate p term) p term where
    applyPredicate = Apply
    foldPredicate f (Apply p ts) = f p ts
    foldPredicate _ (Equal _ _) = error "foldPredicate - found Equate"
instance (IsPredicate p, HasBoolean p) => HasEquate (NPredicate p term) p term where
    equate = Equal
    foldEquate' eq (Equal t1 t2) = Just (eq t1 t2)
    foldEquate' _ _ = Nothing
{-
instance (IsPredicate p, HasBoolean p) => HasEquate (NPredicate p (NTerm v f)) p (NTerm v f) where
    equate = Equal
    foldEquate' eq (Equal lhs rhs) = Just (eq lhs rhs)
    foldEquate' _ _ = Nothing
-}
instance HasFixity (NPredicate p (NTerm v f)) where
    fixity _ = rootFixity
instance HasBoolean p => HasBoolean (NPredicate p (NTerm v f)) where
    fromBool x = Apply (fromBool x) []
    asBool (Apply p []) = asBool p
    asBool _ = Nothing
instance HasBoolean p => HasBoolean (NFormula v p f) where
    asBool (Predicate (Apply p [])) = asBool p
    asBool _ = Nothing
    fromBool = Predicate . fromBool
instance (IsVariable v, IsPredicate p, IsFunction f, Pretty (NPredicate p (NTerm v f)), HasBoolean p
         ) => IsFormula (NFormula v p f) (NPredicate p (NTerm v f)) where
    atomic = Predicate
    onatoms f (Combine ((:~:) fm)) = Combine ((:~:) (onatoms f fm))
    onatoms f (Combine (BinOp lhs op rhs)) = Combine (BinOp (onatoms f lhs) op (onatoms f rhs))
    onatoms f (Quant op v fm) = Quant op v (onatoms f fm)
    onatoms f (Predicate p) = f p
    overatoms f (Combine ((:~:) fm)) b = overatoms f fm b
    overatoms f (Combine (BinOp lhs _ rhs)) b = overatoms f lhs (overatoms f rhs b)
    overatoms f (Quant _ _ fm) b = overatoms f fm b
    overatoms f (Predicate p) b = f p b
instance (IsVariable v, IsPredicate p, IsFunction f, HasBoolean p, atom ~ NPredicate p (NTerm v f), Pretty atom {-FOL p (NTerm v f)-}
         ) => IsQuantified (NFormula v p f) atom v where
    foldQuantified qu _ _ _ (Quant op v fm) = qu op v fm
    foldQuantified _ co tf at fm = foldPropositional' (error "FIXME - need other function in case of embedded quantifiers") co tf at fm
    quant = Quant
instance (IsVariable v, IsPredicate p, IsFunction f, HasBoolean p, atom ~ NPredicate p (NTerm v f) {-FOL p (NTerm v f)-}, Pretty atom
         ) => IsLiteral (NFormula v p f) atom where
    foldLiteral ne _tf at fm =
        case fm of
          Combine ((:~:) fm') -> ne fm'
          Predicate x -> at x
          _ -> error ("foldLiteral NFormula - unexpected: " ++ prettyShow fm)
instance (IsVariable v, IsPredicate p, IsFunction f, HasBoolean p,
          HasPredicate (NPredicate p (NTerm v f)) p (NTerm v f),
          HasFunctions (NTerm v f) f,
          HasFunctions (NFormula v p f) f,
          Pretty (NPredicate p (NTerm v f)) {-FOL p (NTerm v f)-}
          -- term ~ (NTerm v f),
          -- atom ~ NPredicate p term,
          -- formula ~ (NFormula v p f)
         ) => IsFirstOrder (NFormula v p f) (NPredicate p (NTerm v f)) p (NTerm v f) v f

instance (IsFirstOrder (NFormula v p f) (NPredicate p (NTerm v f)) p (NTerm v f) v f,
          HasPredicate (NPredicate p (NTerm v f)) p (NTerm v f),
          IsTerm (NTerm v f) v f,
          HasFunctions (NTerm v f) f
         ) => HasFunctions (NFormula v p f) f where
    funcs = error "FIXME: HasFunctions (NFormula v p f) f"

instance IsFunction f => HasFunctions (NTerm v f) f where
    funcs = error "FIXME: HasFunctions (NTerm v f)"

instance (IsVariable v, IsFunction f) => IsTerm (NTerm v f) v f where
    vt = NVar
    fApp = FunApp
    foldTerm vf _ (NVar v) = vf v
    foldTerm _ ff (FunApp f ts) = ff f ts
    zipTerms vf ff t1 t2 =
        foldTerm vf' ff' t1
        where
          vf' v1 = foldTerm (\v2 -> Just (vf v1 v2)) (\_ _ -> Nothing) t2
          ff' f1 ts1 = foldTerm (\_ -> Nothing) (\f2 ts2 -> if length ts1 == length ts2 then Just (ff f1 ts1 f2 ts2) else Nothing) t2

$(deriveSafeCopy 1 'base ''Combination)
$(deriveSafeCopy 1 'base ''BinOp)
$(deriveSafeCopy 1 'base ''Quant)
$(deriveSafeCopy 1 'base ''NFormula)
$(deriveSafeCopy 1 'base ''NPredicate)
$(deriveSafeCopy 1 'base ''NTerm)
$(deriveSafeCopy 1 'base ''V)
