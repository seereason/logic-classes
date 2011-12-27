{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrderEq where

import Data.Function (on)
import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants (fromBool)
import Data.Logic.Classes.Equals (AtomEq(..), (.=.), pApp)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula(..), Quant(..), quant)
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Term (Term(..), showTerm, prettyTerm, convertTerm)
import Data.Monoid (mappend)
import qualified Data.Set as S
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)


-- |Find the free (unquantified) variables in a formula.
freeVarsEq :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> S.Set v
freeVarsEq f =
    foldFirstOrder
          (\_ v x -> S.delete v (freeVarsEq x))                    
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` freeVarsEq) x y
                 (:~:) f' -> freeVarsEq f'
          )
          (foldAtomEq (\ _ ts -> S.unions (fmap freeVarsOfTerm ts)) (const S.empty) (\ t1 t2 -> S.union (freeVarsOfTerm t1) (freeVarsOfTerm t2)))
          f
    where
      freeVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- |Find the free and quantified variables in a formula.
allVarsEq :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => formula -> S.Set v
allVarsEq f =
    foldFirstOrder
          (\_ v x -> S.insert v (allVarsEq x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` allVarsEq) x y
                 (:~:) f' -> freeVarsEq f'
          )
          (foldAtomEq (\ _ ts -> S.unions (fmap allVarsOfTerm ts)) (const S.empty) (\ t1 t2 -> S.union (allVarsOfTerm t1) (allVarsOfTerm t2)))
          f
    where
      allVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- |Replace each free occurrence of variable old with term new.
substituteEq :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f) => v -> term -> formula -> formula
substituteEq old new formula =
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
                           (BinOp f1 op f2) -> combine (BinOp (substitute' f1) op (substitute' f2))
                )
                (foldAtomEq (\ p ts -> pApp p (map st ts)) fromBool (\ t1 t2 -> (st t1) .=. (st t2)))
      st t = foldTerm sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else vt v

-- |Convert any instance of a first order logic expression to any other.
convertFOFEq :: forall formula1 atom1 term1 v1 p1 f1 formula2 atom2 term2 v2 p2 f2.
                (FirstOrderFormula formula1 atom1 v1, AtomEq atom1 p1 term1, Term term1 v1 f1,
                 FirstOrderFormula formula2 atom2 v2, AtomEq atom2 p2 term2, Term term2 v2 f2) =>
                (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertFOFEq convertV convertP convertF formula =
    foldFirstOrder q c p formula
    where
      convert' = convertFOFEq convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      q x v f = quant x (convertV v) (convert' f)
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p = foldAtomEq (\ x ts -> pApp (convertP x) (map convertTerm' ts)) fromBool (\ t1 t2 -> (convertTerm' t1) .=. (convertTerm' t2))

-- | Display a formula in a format that can be read into the interpreter.
showFirstOrderEq :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Show v, Show p, Show f) => 
                    formula -> String
showFirstOrderEq formula =
    foldFirstOrder q c a formula
    where
      q Forall v f = "(for_all " ++ show v ++ " " ++ showFirstOrderEq f ++ ")"
      q Exists v f = "(exists " ++  show v ++ " " ++ showFirstOrderEq f ++ ")"
      c (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      c ((:~:) f) = "((.~.) " ++ showFirstOrderEq f ++ ")"
      a :: atom -> String
      a = foldAtomEq (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))")
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
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyFirstOrderEq pv pp pf 5 f
          )
          pr
          formula
    where
      pr :: atom -> Doc
      pr = foldAtomEq (\ p ts -> pp p <> case ts of
                                           [] -> empty
                                           _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                      (\ x -> text (if x then "true" else "false"))
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
    foldFirstOrder (\ _ _ _ -> error "toLiteral q") c p formula
    where
      c :: Combination formula -> lit
      c ((:~:) f) =  (.~.) (fromFirstOrderEq cv cp cf f)
      c _ = error "FirstOrderEq -> Literal"
      p :: atom -> lit
      p = foldAtomEq (\ pr ts -> Data.Logic.Classes.Literal.atomic (applyEq (cp pr) (map ct ts))) fromBool (\ a b -> Data.Logic.Classes.Literal.atomic (ct a `equals` ct b))
      ct = convertTerm cv cf

prettyLitEq :: forall lit atom term v p f. (Literal lit atom v, AtomEq atom p term, Term term v f) =>
              (v -> Doc)
           -> (p -> Doc)
           -> (f -> Doc)
           -> Int
           -> lit
           -> Doc
prettyLitEq pv pp pf prec lit =
    foldLiteral c p lit
    where
      c x = if negated x then text {-"¬"-} "~" <> prettyLitEq pv pp pf 5 x else prettyLitEq pv pp pf 5 x
      p = foldAtomEq (\ pr ts -> 
                          pp pr <> case ts of
                                     [] -> empty
                                     _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                     (\ x -> text (if x then "true" else "false"))
                     (\ t1 t2 -> parensIf (prec > 6) (prettyTerm pv pf t1 <+> text "=" <+> prettyTerm pv pf t2))
      parensIf False = id
      parensIf _ = parens . nest 1
