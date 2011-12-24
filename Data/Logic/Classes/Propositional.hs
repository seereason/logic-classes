-- | PropositionalFormula is a multi-parameter type class for
-- representing instance of propositional (aka zeroth order) logic
-- datatypes.  These are formulas which have truth values, but no "for
-- all" or "there exists" quantifiers and thus no variables or terms
-- as we have in first order or predicate logic.  It is intended that
-- we will be able to write instances for various different
-- implementations to allow these systems to interoperate.  The
-- operator names were adopted from the Logic-TPTP package.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Logic.Classes.Propositional
    ( PropositionalFormula(..)
    , showPropositional
    , convertProp
    , combine
    , negationNormalForm
    , clauseNormalForm
    , clauseNormalForm'
    , clauseNormalFormAlt
    , clauseNormalFormAlt'
    , disjunctiveNormalForm
    , disjunctiveNormalForm'
    ) where

import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Negate
import Data.SafeCopy (base, deriveSafeCopy)
import qualified Data.Set.Extra as Set
import Happstack.Data (deriveNewData)

-- |A type class for propositional logic.  If the type we are writing
-- an instance for is a zero-order (aka propositional) logic type
-- there will generally by a type or a type parameter corresponding to
-- atom.  For first order or predicate logic types, it is generally
-- easiest to just use the formula type itself as the atom type, and
-- raise errors in the implementation if a non-atomic formula somehow
-- appears where an atomic formula is expected (i.e. as an argument to
-- atomic or to the third argument of foldPropositional.)
class (Combinable formula, Constants formula, Ord formula, Ord atom) => PropositionalFormula formula atom | formula -> atom where
    -- | Build an atomic formula from the atom type.
    atomic :: atom -> formula
    -- | A fold function that distributes different sorts of formula
    -- to its parameter functions, one to handle binary operators, one
    -- for negations, and one for atomic formulas.  See examples of its
    -- use to implement the polymorphic functions below.
    foldPropositional :: (Combination formula -> r)
                      -> (atom -> r)
                      -> formula
                      -> r

-- | Show a formula in a format that can be evaluated 
showPropositional :: (PropositionalFormula formula atom) => (atom -> String) -> formula -> String
showPropositional showAtom formula =
    foldPropositional c a formula
    where
      c ((:~:) f) = "(.~.) " ++ parenForm f
      c (BinOp f1 op f2) = parenForm f1 ++ " " ++ showFormOp op ++ " " ++ parenForm f2
      c TRUE = "true"
      c FALSE = "false"
      a = showAtom
      parenForm x = "(" ++ showPropositional showAtom x ++ ")"
      showFormOp (:<=>:) = ".<=>."
      showFormOp (:=>:) = ".=>."
      showFormOp (:&:) = ".&."
      showFormOp (:|:) = ".|."

-- |Convert any instance of a propositional logic expression to any
-- other using the supplied atom conversion function.
convertProp :: forall formula1 atom1 formula2 atom2.
               (PropositionalFormula formula1 atom1,
                PropositionalFormula formula2 atom2) =>
               (atom1 -> atom2) -> formula1 -> formula2
convertProp convertA formula =
    foldPropositional c a formula
    where
      convert' = convertProp convertA
      c ((:~:) f) = (.~.) (convert' f)
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c TRUE = true
      c FALSE = false
      a = atomic . convertA

-- | Simplify and recursively apply nnf.
negationNormalForm :: PropositionalFormula formula atom => formula -> formula
negationNormalForm = nnf . psimplify

-- |Eliminate => and <=> and move negations inwards:
-- 
-- @
-- Formula      Rewrites to
--  P => Q      ~P | Q
--  P <=> Q     (P & Q) | (~P & ~Q)
-- ~∀X P        ∃X ~P
-- ~∃X P        ∀X ~P
-- ~(P & Q)     (~P | ~Q)
-- ~(P | Q)     (~P & ~Q)
-- ~~P  P
-- @
-- 
nnf :: PropositionalFormula formula atom => formula -> formula
nnf fm =
    foldPropositional (nnfCombine fm) (\ _ -> fm) fm

nnfCombine :: PropositionalFormula r atom => r -> Combination r -> r
nnfCombine fm ((:~:) p) = foldPropositional nnfNotCombine (\ _ -> fm) p
nnfCombine _ (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
nnfCombine _ (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
nnfCombine _ (BinOp p (:&:) q) = nnf p .&. nnf q
nnfCombine _ (BinOp p (:|:) q) = nnf p .|. nnf q
nnfCombine fm TRUE = fm
nnfCombine fm FALSE = fm

nnfNotCombine :: PropositionalFormula formula atom => Combination formula -> formula
nnfNotCombine ((:~:) p) = nnf p
nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q
nnfNotCombine TRUE = false
nnfNotCombine FALSE = true

-- |Do a bottom-up recursion to simplify a propositional formula.
psimplify :: PropositionalFormula formula atom => formula -> formula
psimplify fm =
    foldPropositional c a fm
    where
      c ((:~:) p) = psimplify1 ((.~.) (psimplify p))
      c (BinOp p (:&:) q) = psimplify1 (psimplify p .&. psimplify q)
      c (BinOp p (:|:) q) = psimplify1 (psimplify p .|. psimplify q)
      c (BinOp p (:=>:) q) = psimplify1 (psimplify p .=>. psimplify q)
      c (BinOp p (:<=>:) q) = psimplify1 (psimplify p .<=>. psimplify q)
      c TRUE = true
      c FALSE = false
      a _ = fm

-- |Do one step of simplify for propositional formulas:
-- Perform the following transformations everywhere, plus any
-- commuted versions for &, |, and <=>.
-- 
-- @
--  ~False      -> True
--  ~True       -> False
--  True & P    -> P
--  False & P   -> False
--  True | P    -> True
--  False | P   -> P
--  True => P   -> P
--  False => P  -> True
--  P => True   -> P
--  P => False  -> True
--  True <=> P  -> P
--  False <=> P -> ~P
-- @
-- 
psimplify1 :: forall formula atom. PropositionalFormula formula atom => formula -> formula
psimplify1 fm =
    foldPropositional simplifyCombine (\ _ -> fm) fm
    where
      simplifyCombine ((:~:) f) = foldPropositional simplifyNotCombine simplifyNotAtom f
      simplifyCombine (BinOp l op r) =
          case (asBool l, op, asBool r) of
            (Just True,  (:&:), _)            -> r
            (Just False, (:&:), _)            -> fromBool False
            (_,          (:&:), Just True)    -> l
            (_,          (:&:), Just False)   -> fromBool False
            (Just True,  (:|:), _)            -> fromBool True
            (Just False, (:|:), _)            -> r
            (_,          (:|:), Just True)    -> fromBool True
            (_,          (:|:), Just False)   -> l
            (Just True,  (:=>:), _)           -> r
            (Just False, (:=>:), _)           -> fromBool True
            (_,          (:=>:), Just True)   -> fromBool True
            (_,          (:=>:), Just False)  -> (.~.) l
            (Just True,  (:<=>:), _)          -> r
            (Just False, (:<=>:), _)          -> (.~.) r
            (_,          (:<=>:), Just True)  -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _                                 -> fm
      simplifyCombine TRUE = fromBool True
      simplifyCombine FALSE = fromBool False
      simplifyNotCombine ((:~:) f) = f
      simplifyNotCombine TRUE = fromBool False
      simplifyNotCombine FALSE = fromBool True
      simplifyNotCombine _ = fm
      simplifyNotAtom x = (.~.) (atomic x)
      -- We don't require an Eq instance, but we do require Ord so that
      -- we can make sets.
      asBool :: formula -> Maybe Bool
      asBool x =
          case compare x (fromBool True) of
            EQ -> Just True
            _ -> case compare x (fromBool False) of
                   EQ -> Just False
                   _ -> Nothing

clauseNormalForm' :: (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
clauseNormalForm' = simp purecnf . negationNormalForm

clauseNormalForm :: forall formula atom. (PropositionalFormula formula atom) => formula -> formula
clauseNormalForm formula =
    case clean (lists cnf) of
      [] -> fromBool True
      xss -> foldr1 (.&.) . map (foldr1 (.|.)) $ xss
    where
      clean = filter (not . null)
      lists = Set.toList . Set.map Set.toList
      cnf = clauseNormalForm' formula

-- |I'm not sure of the clauseNormalForm functions above are wrong or just different.
clauseNormalFormAlt' :: (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
clauseNormalFormAlt' = simp purecnf' . negationNormalForm

clauseNormalFormAlt :: forall formula atom. (PropositionalFormula formula atom) => formula -> formula
clauseNormalFormAlt formula =
    case clean (lists cnf) of
      [] -> fromBool True
      xss -> foldr1 (.&.) . map (foldr1 (.|.)) $ xss
    where
      clean = filter (not . null)
      lists = Set.toList . Set.map Set.toList
      cnf = clauseNormalFormAlt' formula

disjunctiveNormalForm :: (PropositionalFormula formula atom) => formula -> formula
disjunctiveNormalForm formula =
    case clean (lists dnf) of
      [] -> fromBool False
      xss -> foldr1 (.|.) . map (foldr1 (.&.)) $ xss
    where
      clean = filter (not . null)
      lists = Set.toList . Set.map Set.toList
      dnf = disjunctiveNormalForm' formula

disjunctiveNormalForm' :: (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
disjunctiveNormalForm' = simp purednf . negationNormalForm

simp :: forall formula atom. (PropositionalFormula formula atom) =>
        (formula -> Set.Set (Set.Set formula)) -> formula -> Set.Set (Set.Set formula)
simp purenf fm =
    case (compare fm (fromBool False), compare fm (fromBool True)) of
      (EQ, _) -> Set.empty
      (_, EQ) -> Set.singleton Set.empty
      _ ->cjs'
    where
      -- Discard any clause that is the proper subset of another clause
      cjs' = Set.filter keep cjs
      keep x = not (Set.or (Set.map (Set.isProperSubsetOf x) cjs))
      cjs = Set.filter (not . trivial) (purenf (nnf fm)) :: Set.Set (Set.Set formula)

-- |Harrison page 59.  Look for complementary pairs in a clause.
trivial :: (Negatable lit, Ord lit) => Set.Set lit -> Bool
trivial lits =
    not . Set.null $ Set.intersection (Set.map (.~.) n) p
    where (n, p) = Set.partition negated lits

--purecnf :: forall formula term v p f lit. (FirstOrderFormula formula term v p f, Literal lit term v p f) => formula -> Set.Set (Set.Set lit)
purecnf :: forall formula atom. PropositionalFormula formula atom => formula -> Set.Set (Set.Set formula)
purecnf fm = Set.map (Set.map (.~.)) (purednf (nnf ((.~.) fm)))

purednf :: forall formula atom. (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
purednf fm =
    foldPropositional c (\ _ -> x)  fm
    where
      c :: Combination formula -> Set.Set (Set.Set formula)
      c (BinOp p (:&:) q) = Set.distrib (purednf p) (purednf q)
      c (BinOp p (:|:) q) = Set.union (purednf p) (purednf q)
      c _ = x
      x :: Set.Set (Set.Set formula)
      x = Set.singleton (Set.singleton (convertProp id fm)) :: Set.Set (Set.Set formula)

purecnf' :: forall formula atom. (PropositionalFormula formula atom) => formula -> Set.Set (Set.Set formula)
purecnf' fm =
    foldPropositional c (\ _ -> x)  fm
    where
      c :: Combination formula -> Set.Set (Set.Set formula)
      c (BinOp p (:&:) q) = Set.union (purecnf' p) (purecnf' q)
      c (BinOp p (:|:) q) = Set.distrib (purecnf' p) (purecnf' q)
      c _ = x
      x :: Set.Set (Set.Set formula)
      x = Set.singleton (Set.singleton (convertProp id fm)) :: Set.Set (Set.Set formula)

$(deriveSafeCopy 1 'base ''BinOp)
$(deriveSafeCopy 1 'base ''Combination)

$(deriveNewData [''BinOp, ''Combination])
