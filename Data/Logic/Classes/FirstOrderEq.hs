{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrderEq
    ( showFirstOrderEq
    , fromFirstOrderEq
    , prettyAtomEq
    ) where

import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants (fromBool, ifElse)
import Data.Logic.Classes.Equals (AtomEq(..), applyEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term (Term(..), showTerm, prettyTerm, convertTerm)
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

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

prettyAtomEq :: (AtomEq atom p term, Term term v f) => (v -> Doc) -> (p -> Doc) -> (f -> Doc) -> Int -> atom -> Doc
prettyAtomEq pv pp pf prec atom =
    foldAtomEq (\ p ts -> pp p <> case ts of
                                    [] -> empty
                                    _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
               (text . ifElse "true" "false")
               (\ t1 t2 -> parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2))
               atom
    where
      parensIf False = id
      parensIf _ = parens . nest 1

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
