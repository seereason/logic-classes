{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrder
    ( IsQuantified(..)
    , Quant(..)
    , zipFirstOrder
    , for_all'
    , exists'
    , (!)
    , (?)
    , (∀)
    , (∃)
    , quant'
    , convertFOF
    , toPropositional
    , withUnivQuants
    , showFirstOrder
    , prettyFirstOrder
    , fixityFirstOrder
    , overatomsFirstOrder
    , onatomsFirstOrder
    , atom_union
    , fromFirstOrder
    , fromLiteral
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Formula (IsFormula(atomic, overatoms))
import Data.Logic.Classes.Literal (IsLiteral, foldLiteral)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), Fixity(..), FixityDirection(..))
import qualified Data.Logic.Classes.Propositional as P
import Data.Logic.Classes.Variable (IsVariable)
import Data.Logic.Failing (Failing(..))
import Data.SafeCopy (base, deriveSafeCopy)
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, (<>), (<+>), text, parens, nest)

-- |The 'IsQuantified' type class.  Minimal implementation:
-- @for_all, exists, foldQuantified, foldTerm, (.=.), pApp0-pApp7, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (IsQuantified Formula atom V)@ because the
-- function doesn't mention the Term type.
class ( IsFormula formula atom
      , IsCombinable formula  -- Basic logic operations
      , HasBoolean formula
      , HasBoolean atom
      , HasFixity atom
      , IsVariable v
      , Pretty atom, Pretty v
      ) => IsQuantified formula atom v | formula -> atom v where
    quant :: Quant -> v -> formula -> formula

    for_all :: v -> formula -> formula
    for_all = quant (:!:)
    exists ::  v -> formula -> formula
    exists = quant (:?:)

    -- | A fold function similar to the one in 'PropositionalFormula'
    -- but extended to cover both the existing formula types and the
    -- ones introduced here.  @foldQuantified (.~.) quant binOp infixPred pApp@
    -- is a no op.  The argument order is taken from Logic-TPTP.
    foldQuantified :: (Quant -> v -> formula -> r)
                   -> (Combination formula -> r)
                   -> (Bool -> r)
                   -> (atom -> r)
                   -> formula
                   -> r

zipFirstOrder :: IsQuantified formula atom v =>
                 (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
              -> (Combination formula -> Combination formula -> Maybe r)
              -> (Bool -> Bool -> Maybe r)
              -> (atom -> atom -> Maybe r)
              -> formula -> formula -> Maybe r
zipFirstOrder qu co tf at fm1 fm2 =
    foldQuantified qu' co' tf' at' fm1
    where
      qu' op1 v1 p1 = foldQuantified (qu op1 v1 p1) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      co' c1 = foldQuantified (\ _ _ _ -> Nothing) (co c1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldQuantified (\ _ _ _ -> Nothing) (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' atom1 = foldQuantified (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at atom1) fm2

-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Data.Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = (:!:) -- ^ for_all
           | (:?:) -- ^ exists
             deriving (Eq,Ord,Data,Typeable,Enum,Bounded, Show)

{-
instance Show Quant where
    show (:!:) = "for_all"
    show (:?:) = "exists"
-}

-- |for_all with a list of variables, for backwards compatibility.
for_all' :: IsQuantified formula atom v => [v] -> formula -> formula
for_all' vs f = foldr for_all f vs

-- |exists with a list of variables, for backwards compatibility.
exists' :: IsQuantified formula atom v => [v] -> formula -> formula
exists' vs f = foldr for_all f vs

-- |Names for for_all and exists inspired by the conventions of the
-- TPTP project.
(!) :: IsQuantified formula atom v => v -> formula -> formula
(!) = for_all
(?) :: IsQuantified formula atom v => v -> formula -> formula
(?) = exists

-- Irrelevant, because these are always used as prefix operators, never as infix.
infixr 9 !, ?, ∀, ∃

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: IsQuantified formula atom v => v -> formula -> formula
(∀) = for_all
(∃) :: IsQuantified formula atom v => v -> formula -> formula
(∃) = exists

-- |Legacy version of quant from when we supported lists of quantified
-- variables.  It also has the virtue of eliding quantifications with
-- empty variable lists (by calling for_all' and exists'.)
quant' :: IsQuantified formula atom v => 
         Quant -> [v] -> formula -> formula
quant' (:!:) = for_all'
quant' (:?:) = exists'

convertFOF :: (IsQuantified formula1 atom1 v1, IsQuantified formula2 atom2 v2) =>
              (atom1 -> atom2) -> (v1 -> v2) -> formula1 -> formula2
convertFOF convertA convertV formula =
    foldQuantified qu co tf (atomic . convertA) formula
    where
      convert' = convertFOF convertA convertV
      qu x v f = quant x (convertV v) (convert' f)
      co (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      co ((:~:) f) = combine ((:~:) (convert' f))
      tf = fromBool

-- |Try to convert a first order logic formula to propositional.  This
-- will return Nothing if there are any quantifiers, or if it runs
-- into an atom that it is unable to convert.
toPropositional :: forall formula1 atom v formula2 atom2.
                   (IsQuantified formula1 atom v,
                    P.IsPropositional formula2 atom2) =>
                   (atom -> atom2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldQuantified qu co tf at formula
    where
      convert' = toPropositional convertAtom
      qu _ _ _ = error "toPropositional: invalid argument"
      co (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      co ((:~:) f) = combine ((:~:) (convert' f))
      tf = fromBool
      at = atomic . convertAtom

-- | Display a formula in a format that can be read into the interpreter.
showFirstOrder :: forall formula atom v. (IsQuantified formula atom v, Show v) => (atom -> String) -> formula -> String
showFirstOrder sa formula =
    foldQuantified qu co tf at formula
    where
      qu (:!:) v f = "(for_all " ++ show v ++ " " ++ showFirstOrder sa f ++ ")"
      qu (:?:) v f = "(exists " ++  show v ++ " " ++ showFirstOrder sa f ++ ")"
      co (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      co ((:~:) f) = "((.~.) " ++ showFirstOrder sa f ++ ")"
      tf x = if x then "true" else "false"
      at :: atom -> String
      at = sa
      parenForm x = "(" ++ showFirstOrder sa x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

prettyFirstOrder :: forall formula atom v. (IsQuantified formula atom v) =>
                      (Int -> atom -> Doc) -> (v -> Doc) -> Int -> formula -> Doc
prettyFirstOrder pa pv pprec formula =
    parensIf (pprec > prec) $
    foldQuantified
          (\ qop v f -> prettyQuant qop <> pv v <> text "." <+> (prettyFirstOrder pa pv prec f))
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> (prettyFirstOrder pa pv 2 f1 <+> pPrint op <+> prettyFirstOrder pa pv prec f2)
                       (:<=>:) -> (prettyFirstOrder pa pv 2 f1 <+> pPrint op <+> prettyFirstOrder pa pv prec f2)
                       (:&:) -> (prettyFirstOrder pa pv 3 f1 <+> pPrint op <+> prettyFirstOrder pa pv prec f2)
                       (:|:) -> (prettyFirstOrder pa pv 4 f1 <+> pPrint op <+> prettyFirstOrder pa pv prec f2)
                 ((:~:) f) -> text "¬" {-"~"-} <> prettyFirstOrder pa pv prec f)
          (text . ifElse "true" "false")
          (pa prec)
          formula
    where
      Fixity prec _ = fixityFirstOrder formula
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant (:!:) = text "∀"
      prettyQuant (:?:) = text "∃"

fixityFirstOrder :: (HasFixity atom, IsQuantified formula atom v) => formula -> Fixity
fixityFirstOrder formula =
    foldQuantified qu co tf at formula
    where
      qu _ _ _ = Fixity 10 InfixN
      co ((:~:) _) = Fixity 5 InfixN
      co (BinOp _ (:&:) _) = Fixity 4 InfixL
      co (BinOp _ (:|:) _) = Fixity 3 InfixL
      co (BinOp _ (:=>:) _) = Fixity 2 InfixR
      co (BinOp _ (:<=>:) _) = Fixity 1 InfixL
      tf _ = Fixity 10 InfixN
      at = fixity

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

-- ------------------------------------------------------------------------- 
-- Apply a function to the atoms, otherwise keeping structure.               
-- ------------------------------------------------------------------------- 

onatomsFirstOrder :: forall formula atom v. IsQuantified formula atom v => (atom -> formula) -> formula -> formula
onatomsFirstOrder f fm =
    foldQuantified qu co tf at fm
    where
      qu op v p = quant op v (onatomsFirstOrder f p)
      co ((:~:) p) = onatomsFirstOrder f p
      co (BinOp p op q) = binop (onatomsFirstOrder f p) op (onatomsFirstOrder f q)
      tf flag = fromBool flag
      at x = f x

-- ------------------------------------------------------------------------- 
-- Formula analog of list iterator "itlist".                                 
-- -------------------------------------------------------------------------

-- overatomsFirstOrder :: IsQuantified fof atom v => (r -> atom -> r) -> r -> fof -> r
-- overatomsFirstOrder f i fof =
overatomsFirstOrder :: forall fof atom v r. IsQuantified fof atom v => (atom -> r -> r) -> fof -> r -> r
overatomsFirstOrder f fof r0 =
        foldQuantified qu co (const r0) (flip f r0) fof
        where
          qu _ _ fof' = overatomsFirstOrder f fof' r0
          co ((:~:) fof') = overatomsFirstOrder f fof' r0
          co (BinOp p _ q) = overatomsFirstOrder f p (overatomsFirstOrder f q r0)

-- ------------------------------------------------------------------------- 
-- Special case of a union of the results of a function over the atoms.      
-- ------------------------------------------------------------------------- 

atom_union :: forall formula atom v a. (IsQuantified formula atom v, Ord a) =>
              (atom -> Set.Set a) -> formula -> Set.Set a
atom_union f fm = overatoms (\ h t -> Set.union (f h) t) fm Set.empty

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula atom v lit atom2.
                  (IsFormula lit atom2, IsQuantified formula atom v, IsLiteral lit atom2) =>
                  (atom -> atom2) -> formula -> Failing lit
fromFirstOrder ca formula =
    foldQuantified (\ _ _ _ -> Failure ["fromFirstOrder"]) co (Success . fromBool) (Success . atomic . ca) formula
    where
      co :: Combination formula -> Failing lit
      co ((:~:) f) =  fromFirstOrder ca f >>= return . (.~.)
      co _ = Failure ["fromFirstOrder"]

fromLiteral :: forall lit atom v fof atom2. (IsLiteral lit atom, IsQuantified fof atom2 v) =>
               (atom -> atom2) -> lit -> fof
fromLiteral ca lit = foldLiteral (\ p -> (.~.) (fromLiteral ca p)) fromBool (atomic . ca) lit

$(deriveSafeCopy 1 'base ''Quant)
