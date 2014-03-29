{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrder
    ( FirstOrderFormula(..)
    , Quant(..)
    , zipFirstOrder
    , pApp
    , pApp0
    , pApp1
    , pApp2
    , pApp3
    , pApp4
    , pApp5
    , pApp6
    , pApp7
    , for_all'
    , exists'
    , quant
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
    , foldAtomsFirstOrder
    , mapAtomsFirstOrder
    , onatoms
    , overatoms
    , atom_union
    , fromFirstOrder
    , fromLiteral
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Apply (Apply(..), apply, apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7)
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Formula (Formula(atomic))
import Data.Logic.Classes.Literal (Literal, foldLiteral)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Pretty (Pretty(pretty), HasFixity(..), Fixity(..), FixityDirection(..))
import qualified Data.Logic.Classes.Propositional as P
import Data.Logic.Classes.Variable (Variable)
import Data.Logic.Failing (Failing(..))
import Data.SafeCopy (base, deriveSafeCopy)
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, (<>), (<+>), text, parens, nest)

-- |The 'FirstOrderFormula' type class.  Minimal implementation:
-- @for_all, exists, foldFirstOrder, foldTerm, (.=.), pApp0-pApp7, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderFormula Formula atom V)@ because the
-- function doesn't mention the Term type.
class ( Formula formula atom
      , Combinable formula  -- Basic logic operations
      , Constants formula
      , Constants atom
      , HasFixity atom
      , Variable v
      , Pretty atom, Pretty v
      ) => FirstOrderFormula formula atom v | formula -> atom v where
    -- | Universal quantification - for all x (formula x)
    for_all :: v -> formula -> formula
    -- | Existential quantification - there exists x such that (formula x)
    exists ::  v -> formula -> formula

    -- | A fold function similar to the one in 'PropositionalFormula'
    -- but extended to cover both the existing formula types and the
    -- ones introduced here.  @foldFirstOrder (.~.) quant binOp infixPred pApp@
    -- is a no op.  The argument order is taken from Logic-TPTP.
    foldFirstOrder :: (Quant -> v -> formula -> r)
                   -> (Combination formula -> r)
                   -> (Bool -> r)
                   -> (atom -> r)
                   -> formula
                   -> r

zipFirstOrder :: FirstOrderFormula formula atom v =>
                 (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
              -> (Combination formula -> Combination formula -> Maybe r)
              -> (Bool -> Bool -> Maybe r)
              -> (atom -> atom -> Maybe r)
              -> formula -> formula -> Maybe r
zipFirstOrder qu co tf at fm1 fm2 =
    foldFirstOrder qu' co' tf' at' fm1
    where
      qu' op1 v1 p1 = foldFirstOrder (qu op1 v1 p1) (\ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      co' c1 = foldFirstOrder (\ _ _ _ -> Nothing) (co c1) (\ _ -> Nothing) (\ _ -> Nothing) fm2
      tf' x1 = foldFirstOrder (\ _ _ _ -> Nothing) (\ _ -> Nothing) (tf x1) (\ _ -> Nothing) fm2
      at' atom1 = foldFirstOrder (\ _ _ _ -> Nothing) (\ _ -> Nothing) (\ _ -> Nothing) (at atom1) fm2

-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Data.Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = Forall | Exists deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

pApp :: forall formula atom term v p. (Formula formula atom, Apply atom p term) => p -> [term] -> formula
pApp p ts = atomic (apply p ts :: atom)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> formula
pApp0 p = atomic (apply0 p :: atom)
pApp1 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> formula
pApp1 p a = atomic (apply1 p a :: atom)
pApp2 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> formula
pApp2 p a b = atomic (apply2 p a b :: atom)
pApp3 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = atomic (apply3 p a b c :: atom)
pApp4 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = atomic (apply4 p a b c d :: atom)
pApp5 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = atomic (apply5 p a b c d e :: atom)
pApp6 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = atomic (apply6 p a b c d e f :: atom)
pApp7 :: forall formula atom term p. (Formula formula atom, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
pApp7 p a b c d e f g = atomic (apply7 p a b c d e f g :: atom)

-- |for_all with a list of variables, for backwards compatibility.
for_all' :: FirstOrderFormula formula atom v => [v] -> formula -> formula
for_all' vs f = foldr for_all f vs

-- |exists with a list of variables, for backwards compatibility.
exists' :: FirstOrderFormula formula atom v => [v] -> formula -> formula
exists' vs f = foldr for_all f vs

-- |Names for for_all and exists inspired by the conventions of the
-- TPTP project.
(!) :: FirstOrderFormula formula atom v => v -> formula -> formula
(!) = for_all
(?) :: FirstOrderFormula formula atom v => v -> formula -> formula
(?) = exists

-- Irrelevant, because these are always used as prefix operators, never as infix.
infixr 9 !, ?, ∀, ∃

-- | ∀ can't be a function when -XUnicodeSyntax is enabled.
(∀) :: FirstOrderFormula formula atom v => v -> formula -> formula
(∀) = for_all
(∃) :: FirstOrderFormula formula atom v => v -> formula -> formula
(∃) = exists

-- | Helper function for building folds.
quant :: FirstOrderFormula formula atom v => 
         Quant -> v -> formula -> formula
quant Forall v f = for_all v f
quant Exists v f = exists v f

-- |Legacy version of quant from when we supported lists of quantified
-- variables.  It also has the virtue of eliding quantifications with
-- empty variable lists (by calling for_all' and exists'.)
quant' :: FirstOrderFormula formula atom v => 
         Quant -> [v] -> formula -> formula
quant' Forall = for_all'
quant' Exists = exists'

convertFOF :: (FirstOrderFormula formula1 atom1 v1, FirstOrderFormula formula2 atom2 v2) =>
              (atom1 -> atom2) -> (v1 -> v2) -> formula1 -> formula2
convertFOF convertA convertV formula =
    foldFirstOrder qu co tf (atomic . convertA) formula
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
                   (FirstOrderFormula formula1 atom v,
                    P.PropositionalFormula formula2 atom2) =>
                   (atom -> atom2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldFirstOrder qu co tf at formula
    where
      convert' = toPropositional convertAtom
      qu _ _ _ = error "toPropositional: invalid argument"
      co (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      co ((:~:) f) = combine ((:~:) (convert' f))
      tf = fromBool
      at = atomic . convertAtom

-- | Display a formula in a format that can be read into the interpreter.
showFirstOrder :: forall formula atom v. (FirstOrderFormula formula atom v, Show v) => (atom -> String) -> formula -> String
showFirstOrder sa formula =
    foldFirstOrder qu co tf at formula
    where
      qu Forall v f = "(for_all " ++ show v ++ " " ++ showFirstOrder sa f ++ ")"
      qu Exists v f = "(exists " ++  show v ++ " " ++ showFirstOrder sa f ++ ")"
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

prettyFirstOrder :: forall formula atom v. (FirstOrderFormula formula atom v) =>
                      (Int -> atom -> Doc) -> (v -> Doc) -> Int -> formula -> Doc
prettyFirstOrder pa pv pprec formula =
    parensIf (pprec > prec) $
    foldFirstOrder
          (\ qop v f -> prettyQuant qop <> pv v <> text "." <+> (prettyFirstOrder pa pv prec f))
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> (prettyFirstOrder pa pv 2 f1 <+> pretty op <+> prettyFirstOrder pa pv prec f2)
                       (:<=>:) -> (prettyFirstOrder pa pv 2 f1 <+> pretty op <+> prettyFirstOrder pa pv prec f2)
                       (:&:) -> (prettyFirstOrder pa pv 3 f1 <+> pretty op <+> prettyFirstOrder pa pv prec f2)
                       (:|:) -> (prettyFirstOrder pa pv 4 f1 <+> pretty op <+> prettyFirstOrder pa pv prec f2)
                 ((:~:) f) -> text "¬" {-"~"-} <> prettyFirstOrder pa pv prec f)
          (text . ifElse "true" "false")
          (pa prec)
          formula
    where
      Fixity prec _ = fixityFirstOrder formula
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant Forall = text "∀" -- "!"
      prettyQuant Exists = text "∃" -- "?"

fixityFirstOrder :: (HasFixity atom, FirstOrderFormula formula atom v) => formula -> Fixity
fixityFirstOrder formula =
    foldFirstOrder qu co tf at formula
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
withUnivQuants :: FirstOrderFormula formula atom v => ([v] -> formula -> r) -> formula -> r
withUnivQuants fn formula =
    doFormula [] formula
    where
      doFormula vs f =
          foldFirstOrder
                (doQuant vs)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                f
      doQuant vs Forall v f = doFormula (v : vs) f
      doQuant vs Exists v f = fn (reverse vs) (exists v f)

-- ------------------------------------------------------------------------- 
-- Apply a function to the atoms, otherwise keeping structure.               
-- ------------------------------------------------------------------------- 

mapAtomsFirstOrder :: forall formula atom v. FirstOrderFormula formula atom v => (atom -> formula) -> formula -> formula
mapAtomsFirstOrder f fm =
    foldFirstOrder qu co tf at fm
    where
      qu op v p = quant op v (mapAtomsFirstOrder f p)
      co ((:~:) p) = mapAtomsFirstOrder f p
      co (BinOp p op q) = binop (mapAtomsFirstOrder f p) op (mapAtomsFirstOrder f q)
      tf flag = fromBool flag
      at x = f x

-- | Deprecated - use mapAtoms
onatoms :: forall formula atom v. (FirstOrderFormula formula atom v) => (atom -> formula) -> formula -> formula
onatoms = mapAtomsFirstOrder

-- ------------------------------------------------------------------------- 
-- Formula analog of list iterator "itlist".                                 
-- -------------------------------------------------------------------------

foldAtomsFirstOrder :: FirstOrderFormula fof atom v => (r -> atom -> r) -> r -> fof -> r
foldAtomsFirstOrder f i fof =
        foldFirstOrder qu co (const i) (f i) fof
        where
          qu _ _ fof' = foldAtomsFirstOrder f i fof'
          co ((:~:) fof') = foldAtomsFirstOrder f i fof'
          co (BinOp p _ q) = foldAtomsFirstOrder f (foldAtomsFirstOrder f i q) p

-- | Deprecated - use foldAtoms
overatoms :: forall formula atom v r. FirstOrderFormula formula atom v =>
             (atom -> r -> r) -> formula -> r -> r
overatoms f fm b = foldAtomsFirstOrder (flip f) b fm

-- ------------------------------------------------------------------------- 
-- Special case of a union of the results of a function over the atoms.      
-- ------------------------------------------------------------------------- 

atom_union :: forall formula atom v a. (FirstOrderFormula formula atom v, Ord a) =>
              (atom -> Set.Set a) -> formula -> Set.Set a
atom_union f fm = overatoms (\ h t -> Set.union (f h) t) fm Set.empty

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrder :: forall formula atom v lit atom2.
                  (Formula lit atom2, FirstOrderFormula formula atom v, Literal lit atom2) =>
                  (atom -> atom2) -> formula -> Failing lit
fromFirstOrder ca formula =
    foldFirstOrder (\ _ _ _ -> Failure ["fromFirstOrder"]) co (Success . fromBool) (Success . atomic . ca) formula
    where
      co :: Combination formula -> Failing lit
      co ((:~:) f) =  fromFirstOrder ca f >>= return . (.~.)
      co _ = Failure ["fromFirstOrder"]

fromLiteral :: forall lit atom v fof atom2. (Literal lit atom, FirstOrderFormula fof atom2 v) =>
               (atom -> atom2) -> lit -> fof
fromLiteral ca lit = foldLiteral (\ p -> (.~.) (fromLiteral ca p)) fromBool (atomic . ca) lit

$(deriveSafeCopy 1 'base ''Quant)
