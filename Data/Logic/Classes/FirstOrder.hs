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
{-
    , freeVars
    , quantVars
    , allVars
    , univquant_free_vars
    , substitute
    , substitutePairs
    , disj
    , conj
-}
    ) where

import Data.Generics (Data, Typeable)
import Data.Logic.Classes.Apply (Apply(..), apply, apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7)
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Pretty (Pretty)
import Data.Logic.Classes.Propositional (PropositionalFormula)
import Data.Logic.Classes.Variable (Variable)
import Data.SafeCopy (base, deriveSafeCopy)
import Happstack.Data (deriveNewData)
import Text.PrettyPrint (Doc, (<>), (<+>), text, parens, nest)

-- |The 'FirstOrderFormula' type class.  Minimal implementation:
-- @for_all, exists, foldFirstOrder, foldTerm, (.=.), pApp0-pApp7, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderFormula Formula term V p f)@ because the
-- function doesn't mention the Term type.
class ( Combinable formula  -- Basic logic operations
      , Constants formula
      , Constants atom
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
    atomic :: atom -> formula

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

pApp :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> [term] -> formula
pApp p ts = atomic (apply p ts)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> formula
pApp0 p = atomic (apply0 p)
pApp1 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> formula
pApp1 p a = atomic (apply1 p a)
pApp2 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> formula
pApp2 p a b = atomic (apply2 p a b)
pApp3 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = atomic (apply3 p a b c)
pApp4 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = atomic (apply4 p a b c d)
pApp5 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = atomic (apply5 p a b c d e)
pApp6 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = atomic (apply6 p a b c d e f)
pApp7 :: (FirstOrderFormula formula atom v, Apply atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
pApp7 p a b c d e f g = atomic (apply7 p a b c d e f g)

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

infix 1 !, ?, ∀, ∃

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
                    PropositionalFormula formula2 atom2) =>
                   (formula1 -> formula2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldFirstOrder qu co tf at formula
    where
      convert' = toPropositional convertAtom
      qu _ _ _ = error "toPropositional: invalid argument"
      co (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      co ((:~:) f) = combine ((:~:) (convert' f))
      tf = fromBool
      at _ = convertAtom formula

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
prettyFirstOrder pa pv prec formula =
    foldFirstOrder
          (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop <> pv v <+> prettyFirstOrder pa pv 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyFirstOrder pa pv 2 f1 <+> formOp op <+> prettyFirstOrder pa pv 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyFirstOrder pa pv 2 f1 <+> formOp op <+> prettyFirstOrder pa pv 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyFirstOrder pa pv 3 f1 <+> formOp op <+> prettyFirstOrder pa pv 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyFirstOrder pa pv 4 f1 <+> formOp op <+> prettyFirstOrder pa pv 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyFirstOrder pa pv 5 f)
          (text . ifElse "true" "false")
          (pa 6)
          formula
    where
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant Forall = text {-"∀"-} "!"
      prettyQuant Exists = text {-"∃"-} "?"
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

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

$(deriveSafeCopy 1 'base ''Quant)

$(deriveNewData [''Quant])

