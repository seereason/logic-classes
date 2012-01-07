{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrderEq
    ( substituteEq
    , showFirstOrderEq
    , prettyFirstOrderEq
    , fromFirstOrderEq
    , prettyLitEq
    ) where

import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants (fromBool, ifElse)
import Data.Logic.Classes.Equals (AtomEq(..), applyEq, (.=.), pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..), quant)
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term (Term(..), showTerm, prettyTerm, convertTerm)
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

-- |Replace each free occurrence of variable old with term new.
substitute :: forall formula atom term v f. (FirstOrderFormula formula atom v, Term term v f) => v -> term -> (atom -> formula) -> formula -> formula
substitute old new atom formula =
    foldTerm (\ new' -> if old == new' then formula else substitute' formula)
             (\ _ _ -> substitute' formula)
             new
    where
      substitute' =
          foldFirstOrder -- If the old variable appears in a quantifier
                -- we can stop doing the substitution.
                (\ q v f' -> quant q v (if old == v then f' else substitute' f'))
                (\ cm -> case cm of
                           ((:~:) f') -> combine ((:~:) (substitute' f'))
                           (BinOp f1 op f2) -> combine (BinOp (substitute' f1) op (substitute' f2)))
                fromBool
                atom

-- |Replace each free occurrence of variable old with term new.
substituteEq :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => v -> term -> formula -> formula
substituteEq old new formula =
    substitute old new atom formula
    where 
      atom = foldAtomEq (\ p ts -> pApp p (map st ts)) fromBool (\ t1 t2 -> st t1 .=. st t2)
      st :: term -> term
      st t = foldTerm sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else vt v

-- | Display a formula in a format that can be read into the interpreter.
showFirstOrderEq :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Show v, Show p, Show f) => 
                    formula -> String
showFirstOrderEq formula =
    foldFirstOrder qu co tf at formula
    where
      qu Forall v f = "(for_all " ++ show v ++ " " ++ showFirstOrderEq f ++ ")"
      qu Exists v f = "(exists " ++  show v ++ " " ++ showFirstOrderEq f ++ ")"
      co (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      co ((:~:) f) = "((.~.) " ++ showFirstOrderEq f ++ ")"
      tf x = if x then "true" else "false"
      at :: atom -> String
      at = foldAtomEq (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))")
                      (\ x -> if x then "true" else "false")
                      (\ t1 t2 -> "(" ++ parenTerm t1 ++ " .=. " ++ parenTerm t2 ++ ")")
      parenForm x = "(" ++ showFirstOrderEq x ++ ")"
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

prettyFirstOrderEq :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) =>
                      (v -> Doc) -> (p -> Doc) -> (f -> Doc) -> Int -> formula -> Doc
prettyFirstOrderEq pv pp pf prec formula =
    foldFirstOrder
          (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop <> pv v <+> prettyFirstOrderEq pv pp pf 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyFirstOrderEq pv pp pf 2 f1 <+> formOp op <+> prettyFirstOrderEq pv pp pf 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyFirstOrderEq pv pp pf 2 f1 <+> formOp op <+> prettyFirstOrderEq pv pp pf 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyFirstOrderEq pv pp pf 3 f1 <+> formOp op <+> prettyFirstOrderEq pv pp pf 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyFirstOrderEq pv pp pf 4 f1 <+> formOp op <+> prettyFirstOrderEq pv pp pf 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyFirstOrderEq pv pp pf 5 f)
          (text . ifElse "true" "false")
          pr
          formula
    where
      pr :: atom -> Doc
      pr = foldAtomEq (\ p ts -> pp p <> case ts of
                                           [] -> empty
                                           _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                      (text . ifElse "true" "false")
                      (\ t1 t2 -> parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2))
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant Forall = text {-"∀"-} "!"
      prettyQuant Exists = text {-"∃"-} "?"
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

-- |Just like Logic.FirstOrder.convertFOF except it rejects anything
-- with a construct unsupported in a normal logic formula,
-- i.e. quantifiers and formula combinators other than negation.
fromFirstOrderEq :: forall formula atom term v p f lit atom2 term2 v2 p2 f2.
                  (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Literal lit atom2 v2, AtomEq atom2 p2 term2, Term term2 v2 f2) =>
                  (v -> v2) -> (p -> p2) -> (f -> f2) -> formula -> lit
fromFirstOrderEq cv cp cf formula =
    foldFirstOrder (\ _ _ _ -> error "toLiteral q") co tf at formula
    where
      co :: Combination formula -> lit
      co ((:~:) f) =  (.~.) (fromFirstOrderEq cv cp cf f)
      co _ = error "FirstOrderEq -> Literal"
      tf = fromBool
      at :: atom -> lit
      at = foldAtomEq (\ pr ts -> Data.Logic.Classes.Literal.atomic (applyEq (cp pr) (map ct ts))) fromBool (\ a b -> Data.Logic.Classes.Literal.atomic (ct a `equals` ct b))
      ct = convertTerm cv cf

prettyLitEq :: forall lit atom term v p f. (Literal lit atom v, AtomEq atom p term, Term term v f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLitEq pv pp pf prec lit =
    foldLiteral co tf at lit
    where
      co :: lit -> Doc
      co x = if negated x then text {-"¬"-} "~" <> prettyLitEq pv pp pf 5 x else prettyLitEq pv pp pf 5 x
      tf x = text (if x then "true" else "false")
      at = foldAtomEq (\ pr ts -> 
                           pp pr <> case ts of
                                      [] -> empty
                                      _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                      tf
                      (\ t1 t2 -> parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2))
      parensIf False = id
      parensIf _ = parens . nest 1