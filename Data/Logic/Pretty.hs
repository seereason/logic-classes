{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Data.Logic.Pretty
    ( showForm
    , showTerm
    , prettyForm
    , prettyTerm
    , prettyLit
    , prettyProof
    , prettyINF
    ) where

import Data.List (intercalate, intersperse)
import Data.Logic.FirstOrder (FirstOrderFormula(foldF), Term(foldT), Quant(..))
import Data.Logic.Logic
import qualified Data.Logic.Normal as N -- (Literal(..))
import Data.Logic.Predicate (Predicate(Apply, Constant, Equal, NotEqual))
import qualified Data.Set as Set
import Text.PrettyPrint (Doc, text, (<>), (<+>), empty, parens, hcat, nest, brackets, cat, hsep)

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

prettyTerm :: forall v f term. (Term term v f) =>
              (v -> Doc)
           -> (f -> Doc)
           -> term
           -> Doc
prettyTerm pv pf t = foldT pv (\ fn ts -> pf fn <> brackets (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts)))) t

prettyForm :: forall formula term v p f. (FirstOrderFormula formula term v p f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> formula
           -> Doc
prettyForm pv pp pf prec formula =
    foldF (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop <> pv v <+> prettyForm pv pp pf 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyForm pv pp pf 2 f1 <+> formOp op <+> prettyForm pv pp pf 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyForm pv pp pf 2 f1 <+> formOp op <+> prettyForm pv pp pf 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyForm pv pp pf 3 f1 <+> formOp op <+> prettyForm pv pp pf 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyForm pv pp pf 4 f1 <+> formOp op <+> prettyForm pv pp pf 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyForm pv pp pf 5 f)
          pr
          formula
    where
      pr :: Predicate p term -> Doc
      pr (Constant x) = text (show x)
      pr (Equal t1 t2) = parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2)
      pr (NotEqual t1 t2) = parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "!=" <+> prettyTerm pv pf t2)
      pr (Apply p ts) =
          pp p <> case ts of
                    [] -> empty
                    _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts)))
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant All = text {-"∀"-} "!"
      prettyQuant Exists = text {-"∃"-} "?"
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

prettyLit :: forall lit term v p f. (N.Literal lit term v p f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLit pv pp pf prec lit =
    N.foldN c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLit pv pp pf 5 x else prettyLit pv pp pf 5 x
      p (N.Apply pr ts) =
          pp pr <> case ts of
                        [] -> empty
                        _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts)))
      p (N.Equal t1 t2) = parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2)
      parensIf False = id
      parensIf _ = parens . nest 1

prettyProof :: (Negatable lit, Ord lit) => (lit -> Doc) -> Set.Set (N.ImplicativeNormalForm lit) -> Doc
prettyProof lit p = cat $ [text "["] ++ intersperse (text ", ") (map (prettyINF lit) (Set.toList p)) ++ [text "]"]

prettyINF :: (Negatable lit, Ord lit) => (lit -> Doc) -> N.ImplicativeNormalForm lit -> Doc
prettyINF lit x = cat $ [text "(", hsep (map lit (Set.toList (N.neg x))),
                         text ") => (", hsep (map lit (Set.toList (N.pos x))), text ")"]
