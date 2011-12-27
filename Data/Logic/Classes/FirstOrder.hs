{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrder
    ( FirstOrderFormula(..)
    , Quant(..)
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
    , (!), (?)
    , quant'
    , convertFOF
    , toPropositional
    , showFirstOrder
    , prettyFirstOrder
{-
    , freeVars
    , withUnivQuants
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
import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Atom (Atom(..), apply0, apply1, apply2, apply3, apply4, apply5, apply6, apply7)
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Propositional (PropositionalFormula)
import Data.Logic.Classes.Term (Term(..), showTerm, prettyTerm, convertTerm)
import Data.Logic.Classes.Variable (Variable)
import Data.SafeCopy (base, deriveSafeCopy)
import Happstack.Data (deriveNewData)
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

{-
-- |A class of predicates
class (Combinable formula, Constants p, Arity p) => Pred p term formula | formula -> p, formula -> term where
    pApp0 :: p  -> formula
    pApp1 :: p -> term -> formula
    pApp2 :: p -> term -> term -> formula
    pApp3 :: p -> term -> term -> term -> formula
    pApp4 :: p -> term -> term -> term -> term -> formula
    pApp5 :: p -> term -> term -> term -> term -> term -> formula
    pApp6 :: p -> term -> term -> term -> term -> term -> term -> formula
    pApp7 :: p -> term -> term -> term -> term -> term -> term -> term -> formula
    -- | Equality of Terms
    (.=.) :: term -> term -> formula
    -- | Inequality of Terms
    (.!=.) :: term -> term -> formula
    a .!=. b = (.~.) (a .=. b)
-}

-- |The 'FirstOrderFormula' type class.  Minimal implementation:
-- @for_all, exists, foldFirstOrder, foldTerm, (.=.), pApp0-pApp7, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderFormula Formula term V p f)@ because the
-- function doesn't mention the Term type.
class ( Combinable formula  -- Basic logic operations
      , Data formula        -- Allows us to use Data.Generics functions on formulas
      , Variable v
      , Show v
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
                   -> (atom -> r)
                   -> formula
                   -> r
    zipFirstOrder :: (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
                  -> (Combination formula -> Combination formula -> Maybe r)
                  -> (atom -> atom -> Maybe r)
                  -> formula -> formula -> Maybe r
    atomic :: atom -> formula

-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Data.Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = Forall | Exists deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

pApp :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> [term] -> formula
pApp p ts = atomic (apply p ts)

-- | Versions of pApp specialized for different argument counts.
pApp0 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> formula
pApp0 p = atomic (apply0 p)
pApp1 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> formula
pApp1 p a = atomic (apply1 p a)
pApp2 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> formula
pApp2 p a b = atomic (apply2 p a b)
pApp3 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> term -> formula
pApp3 p a b c = atomic (apply3 p a b c)
pApp4 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> term -> term -> formula
pApp4 p a b c d = atomic (apply4 p a b c d)
pApp5 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> term -> term -> term -> formula
pApp5 p a b c d e = atomic (apply5 p a b c d e)
pApp6 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> term -> term -> term -> term -> formula
pApp6 p a b c d e f = atomic (apply6 p a b c d e f)
pApp7 :: (FirstOrderFormula formula atom v, Atom atom p term) => p -> term -> term -> term -> term -> term -> term -> term -> formula
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

-- |Convert any instance of a first order logic expression to any other.
convertFOF :: forall formula1 atom1 term1 v1 p1 f1 formula2 atom2 term2 v2 p2 f2.
              (FirstOrderFormula formula1 atom1 v1, Atom atom1 p1 term1, Term term1 v1 f1,
               FirstOrderFormula formula2 atom2 v2, Atom atom2 p2 term2, Term term2 v2 f2) =>
              (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertFOF convertV convertP convertF formula =
    foldFirstOrder q c p formula
    where
      convert' = convertFOF convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      q x v f = quant x (convertV v) (convert' f)
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p = foldAtom (\ x ts -> pApp (convertP x) (map convertTerm' ts)) (pApp0 . fromBool)

-- |Try to convert a first order logic formula to propositional.  This
-- will return Nothing if there are any quantifiers, or if it runs
-- into an atom that it is unable to convert.
toPropositional :: forall formula1 atom v formula2 atom2.
                   (FirstOrderFormula formula1 atom v,
                    PropositionalFormula formula2 atom2) =>
                   (formula1 -> formula2) -> formula1 -> formula2
toPropositional convertAtom formula =
    foldFirstOrder q c p formula
    where
      convert' = toPropositional convertAtom
      q _ _ _ = error "toPropositional: invalid argument"
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p _ = convertAtom formula

-- | Display a formula in a format that can be read into the interpreter.
showFirstOrder :: forall formula atom term v p f. (FirstOrderFormula formula atom v, Atom atom p term, Term term v f, Show v, Show p, Show f) => 
                  formula -> String
showFirstOrder formula =
    foldFirstOrder q c a formula
    where
      q Forall v f = "(for_all " ++ show v ++ " " ++ showFirstOrder f ++ ")"
      q Exists v f = "(exists " ++  show v ++ " " ++ showFirstOrder f ++ ")"
      c (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      c ((:~:) f) = "((.~.) " ++ showFirstOrder f ++ ")"
      a = foldAtom (\ p ts -> "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))") (\ x -> if x then "true" else "false")
      parenForm x = "(" ++ showFirstOrder x ++ ")"
      -- parenTerm :: term -> String
      -- parenTerm x = "(" ++ showTerm x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

prettyFirstOrder :: forall formula atom term v p f. (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) =>
                    (v -> Doc)
                 -> (p -> Doc)
                 -> (f -> Doc)
                 -> Int
                 -> formula
                 -> Doc
prettyFirstOrder pv pp pf prec formula =
    foldFirstOrder
          (\ qop v f -> parensIf (prec > 1) $ prettyQuant qop <> pv v <+> prettyFirstOrder pv pp pf 1 f)
          (\ cm ->
               case cm of
                 (BinOp f1 op f2) ->
                     case op of
                       (:=>:) -> parensIf (prec > 2) $ (prettyFirstOrder pv pp pf 2 f1 <+> formOp op <+> prettyFirstOrder pv pp pf 2 f2)
                       (:<=>:) -> parensIf (prec > 2) $ (prettyFirstOrder pv pp pf 2 f1 <+> formOp op <+> prettyFirstOrder pv pp pf 2 f2)
                       (:&:) -> parensIf (prec > 3) $ (prettyFirstOrder pv pp pf 3 f1 <+> formOp op <+> prettyFirstOrder pv pp pf 3 f2)
                       (:|:) -> parensIf {-(prec > 4)-} True $ (prettyFirstOrder pv pp pf 4 f1 <+> formOp op <+> prettyFirstOrder pv pp pf 4 f2)
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyFirstOrder pv pp pf 5 f
          )
          pr
          formula
    where
      pr :: atom -> Doc
      pr = foldAtom (\ p ts ->
                         pp p <> case ts of
                                   [] -> empty
                                   _ -> parens (hcat (intersperse (text ",") (map (prettyTerm pv pf) ts))))
                    (\ x -> text (if x then "true" else "false"))
      parensIf False = id
      parensIf _ = parens . nest 1
      prettyQuant Forall = text {-"∀"-} "!"
      prettyQuant Exists = text {-"∃"-} "?"
      formOp (:<=>:) = text "<=>"
      formOp (:=>:) = text "=>"
      formOp (:&:) = text "&"
      formOp (:|:) = text "|"

{-
-- | Functions to disjunct or conjunct a list.
disj :: FirstOrderFormula formula atom v => [formula] -> formula
disj [] = false
disj [x] = x
disj (x:xs) = x .|. disj xs

conj :: FirstOrderFormula formula atom v => [formula] -> formula
conj [] = true
conj [x] = x
conj (x:xs) = x .&. conj xs

-- |Find the free (unquantified) variables in a formula.
freeVars :: (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) => formula -> S.Set v
freeVars f =
    foldFirstOrder
          (\_ v x -> S.delete v (freeVars x))                    
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` freeVars) x y
                 (:~:) f' -> freeVars f')
          (foldAtom (\ _ ts -> S.unions (fmap freeVarsOfTerm ts)))
          f
    where
      freeVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

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
                f
      doQuant vs Forall v f = doFormula (v : vs) f
      doQuant vs Exists v f = fn (reverse vs) (exists v f)

{-
withImplication :: FirstOrderFormula formula atom v => r -> (formula -> formula -> r) -> formula -> r
withImplication def fn formula =
    foldFirstOrder (\ _ _ _ -> def) c (\ _ -> def) formula
    where
      c (BinOp a (:=>:) b) = fn a b
      c _ = def
-}

-- |Find the variables that are quantified in a formula
quantVars :: FirstOrderFormula formula atom v => formula -> S.Set v
quantVars =
    foldFirstOrder
          (\ _ v x -> S.insert v (quantVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` quantVars) x y
                 ((:~:) f) -> quantVars f)
          (\ _ -> S.empty)

-- |Find the free and quantified variables in a formula.
allVars :: (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) => formula -> S.Set v
allVars f =
    foldFirstOrder
          (\_ v x -> S.insert v (allVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` allVars) x y
                 (:~:) f' -> freeVars f')
          (foldAtom (\ _ ts -> S.unions (fmap allVarsOfTerm ts)))
          f
    where
      allVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else foldr for_all cnf' (S.toList free)
    where free = freeVars cnf'

-- |Replace each free occurrence of variable old with term new.
substitute :: (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) => v -> term -> formula -> formula
substitute old new formula =
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
                (foldAtom (\ p ts -> pApp p (map st ts)))
      st t = foldTerm sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else vt v

substitutePairs :: (FirstOrderFormula formula atom v, Atom atom p term, Term term v f) => [(v, term)] -> formula -> formula
substitutePairs pairs formula = foldr (\ (old, new) f -> substitute old new f) formula pairs 
-}

$(deriveSafeCopy 1 'base ''Quant)

$(deriveNewData [''Quant])

