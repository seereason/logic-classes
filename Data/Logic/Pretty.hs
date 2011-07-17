{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Data.Logic.Pretty
    ( Pretty(pretty)
    , showForm
    , showTerm
    , prettyForm
    , prettyTerm
    , prettyLit
    ) where

import Data.List (intercalate, intersperse)
import Data.Logic.FirstOrder (FirstOrderFormula(foldF), Term(foldT), Quant(..))
import Data.Logic.Logic
import qualified Data.Logic.Normal as N -- (Literal(..))
import Data.Logic.Predicate (Predicate(Apply, Constant, Equal, NotEqual))
import Text.PrettyPrint (Doc, text, (<>), (<+>), empty, parens, hcat, nest, brackets)

class Pretty x where
    pretty :: x -> Doc

-- | Display a formula in a format that can be read into the interpreter.
showForm :: forall formula term v p f. (FirstOrderFormula formula term v p f, Show v, Show p, Show f) => 
            formula -> String
showForm formula =
    foldF q c a formula
    where
      q All v f = "(for_all " ++ show v ++ " " ++ showForm f ++ ")"
      q Exists v f = "(exists " ++  show v ++ " " ++ showForm f ++ ")"
      c (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      c ((:~:) f) = "((.~.) " ++ showForm f ++ ")"
      a :: Predicate p term -> String
      a (Equal t1 t2) =
          "(" ++ parenTerm t1 ++ " .=. " ++ parenTerm t2 ++ ")"
      a (NotEqual t1 t2) =
          "(" ++ parenTerm t1 ++ " .!=. " ++ parenTerm t2 ++ ")"
      a (Constant x) = "pApp' (Constant " ++ show x ++ ")"
      a (Apply p ts) = "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))"
      parenForm x = "(" ++ showForm x ++ ")"
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

showTerm :: forall term v f. (Term term v f, Show v, Show f) =>
            term -> String
showTerm term =
    foldT v f term
    where
      v :: v -> String
      v v' = "var (" ++ show v' ++ ")"
      f :: f -> [term] -> String
      f fn ts = "fApp (" ++ show fn ++ ") [" ++ intercalate "," (map showTerm ts) ++ "]"

prettyTerm :: forall v f term. (Term term v f, Pretty v, Pretty f) => term -> Doc
prettyTerm t = foldT pretty (\ fn ts -> pretty fn <> brackets (hcat (intersperse (text ",") (map prettyTerm ts)))) t

prettyForm :: forall formula term v p f. (FirstOrderFormula formula term v p f, Pretty v, Pretty p, Pretty f) =>
              Int -> formula -> Doc
prettyForm prec formula =
    foldF (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop <> pretty v <+> prettyForm 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyForm 2 f1 <+> formOp op <+> prettyForm 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyForm 3 f1 <+> formOp op <+> prettyForm 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyForm 4 f1 <+> formOp op <+> prettyForm 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyForm 5 f)
          pr
          formula
    where
      pr (Constant x) = text (show x)
      pr (Equal t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "=" <+> prettyTerm t2)
      pr (NotEqual t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "!=" <+> prettyTerm t2)
      pr (Apply p ts) =
          pretty p <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map prettyTerm ts)))
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant All = text {-"∀"-} "!"
      prettyQuant Exists = text {-"∃"-} "?"
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

prettyLit :: forall lit term v p f. (N.Literal lit term v p f, Pretty v, Pretty p, Pretty f) =>
              Int -> lit -> Doc
prettyLit prec lit =
    N.foldN c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLit 5 x else prettyLit 5 x
      p (N.Apply pr ts) =
          pretty pr <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map prettyTerm ts)))
      p (N.Equal t1 t2) = parensIf (prec > 6) (prettyTerm t1 <+> text "=" <+> prettyTerm t2)
      parensIf False = id
      parensIf _ = parens . nest 1
