{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables, TemplateHaskell, UndecidableInstances #-}
module Data.Logic.Classes.FirstOrder
    ( FirstOrderFormula(..)
    , Quant(..)
    , Predicate(..)
    , quant
    , (!), (?)
    , quant'
    , for_all'
    , exists'
    , freeVars
    , withUnivQuants
    , quantVars
    , allVars
    , univquant_free_vars
    , substitute
    , substitutePairs
    , convertFOF
    , toPropositional
    , disj
    , conj
    , showFirstOrder
    , prettyFirstOrder
    ) where

import Data.Function (on)
import Data.Generics (Data, Typeable)
import Data.List (intercalate, intersperse)
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Boolean
import Data.Logic.Classes.Logic
import Data.Logic.Classes.Pred
import Data.Logic.Classes.Propositional
import Data.Logic.Classes.Term
import Data.Monoid (mappend)
import Data.SafeCopy (base, deriveSafeCopy)
import qualified Data.Set as S
import Happstack.Data (deriveNewData)
import Text.PrettyPrint (Doc, (<>), (<+>), text, empty, parens, hcat, nest)

-- |The 'FirstOrderFormula' type class.  Minimal implementation:
-- @for_all, exists, foldFirstOrder, foldTerm, (.=.), pApp0-pApp7, fApp, var@.  The
-- functional dependencies are necessary here so we can write
-- functions that don't fix all of the type parameters.  For example,
-- without them the univquant_free_vars function gives the error @No
-- instance for (FirstOrderFormula Formula term V p f)@ because the
-- function doesn't mention the Term type.
class ( Term term v f
      , Pred p term formula
      , Logic formula  -- Basic logic operations
      , Data formula   -- Allows us to use Data.Generics functions on formulas
      , Show v
      , Data p
      , Boolean p      -- To implement true and false below
      , Arity p        -- To decide how many arguments
      , Eq p           -- Required during resolution
      , Ord p
      , Show p
      -- , Pretty p
      , Ord f
      , Show f
      ) => FirstOrderFormula formula term v p f
                                    | formula -> term
                                    , formula -> v
                                    , formula -> p
                                    , formula -> f
                                    , term -> p where
    -- | Universal quantification - for all x (formula x)
    for_all :: v -> formula -> formula
    -- | Existential quantification - there exists x such that (formula x)
    exists ::  v -> formula -> formula

    -- | A fold function similar to the one in 'PropositionalFormula'
    -- but extended to cover both the existing formula types and the
    -- ones introduced here.  @foldFirstOrder (.~.) quant binOp infixPred pApp@
    -- is a no op.  The argument order is taken from Logic-TPTP.
    foldFirstOrder :: (Quant -> v -> formula -> r)
                   -> (Combine formula -> r)
                   -> (Predicate p term -> r)
                   -> formula
                   -> r
    zipFirstOrder :: (Quant -> v -> formula -> Quant -> v -> formula -> Maybe r)
                  -> (Combine formula -> Combine formula -> Maybe r)
                  -> (Predicate p term -> Predicate p term -> Maybe r)
                  -> formula -> formula -> Maybe r

-- |A temporary type used in the fold method to represent the
-- combination of a predicate and its arguments.  This reduces the
-- number of arguments to foldFirstOrder and makes it easier to manage the
-- mapping of the different instances to the class methods.
data Predicate p term
    = Equal term term
    | NotEqual term term
    | Constant Bool
    | Apply p [term]
    deriving (Eq, Ord, Show, Read, Data, Typeable)

-- |for_all with a list of variables, for backwards compatibility.
for_all' :: FirstOrderFormula formula term v p f => [v] -> formula -> formula
for_all' vs f = foldr for_all f vs

-- |exists with a list of variables, for backwards compatibility.
exists' :: FirstOrderFormula formula term v p f => [v] -> formula -> formula
exists' vs f = foldr for_all f vs

-- | Functions to disjunct or conjunct a list.
disj :: FirstOrderFormula formula term v p f => [formula] -> formula
disj [] = false
disj [x] = x
disj (x:xs) = x .|. disj xs

conj :: FirstOrderFormula formula term v p f => [formula] -> formula
conj [] = true
conj [x] = x
conj (x:xs) = x .&. conj xs

-- | Helper function for building folds.
quant :: FirstOrderFormula formula term v p f => 
         Quant -> v -> formula -> formula
quant All v f = for_all v f
quant Exists v f = exists v f

-- |Legacy version of quant from when we supported lists of quantified
-- variables.  It also has the virtue of eliding quantifications with
-- empty variable lists (by calling for_all' and exists'.)
quant' :: FirstOrderFormula formula term v p f => 
         Quant -> [v] -> formula -> formula
quant' All = for_all'
quant' Exists = exists'

-- |The 'Quant' and 'InfixPred' types, like the BinOp type in
-- 'Data.Logic.Propositional', could be additional parameters to the type
-- class, but it would add additional complexity with unclear
-- benefits.
data Quant = All | Exists deriving (Eq,Ord,Show,Read,Data,Typeable,Enum,Bounded)

-- |Find the free (unquantified) variables in a formula.
freeVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
freeVars f =
    foldFirstOrder
          (\_ v x -> S.delete v (freeVars x))                    
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` freeVars) x y
                 (:~:) f' -> freeVars f')
          (\ pa -> case pa of
                     Constant _ -> S.empty
                     Equal t1 t2 -> S.union (freeVarsOfTerm t1) (freeVarsOfTerm t2)
                     NotEqual t1 t2 -> S.union (freeVarsOfTerm t1) (freeVarsOfTerm t2)
                     Apply _ ts -> S.unions (fmap freeVarsOfTerm ts))
          f
    where
      freeVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap freeVarsOfTerm args))

-- | Examine the formula to find the list of outermost universally
-- quantified variables, and call a function with that list and the
-- formula after the quantifiers are removed.
withUnivQuants :: FirstOrderFormula formula term v p f => ([v] -> formula -> r) -> formula -> r
withUnivQuants fn formula =
    doFormula [] formula
    where
      doFormula vs f =
          foldFirstOrder
                (doQuant vs)
                (\ _ -> fn (reverse vs) f)
                (\ _ -> fn (reverse vs) f)
                f
      doQuant vs All v f = doFormula (v : vs) f
      doQuant vs Exists v f = fn (reverse vs) (exists v f)

{-
withImplication :: FirstOrderFormula formula term v p f => r -> (formula -> formula -> r) -> formula -> r
withImplication def fn formula =
    foldFirstOrder (\ _ _ _ -> def) c (\ _ -> def) formula
    where
      c (BinOp a (:=>:) b) = fn a b
      c _ = def
-}

-- |Find the variables that are quantified in a formula
quantVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
quantVars =
    foldFirstOrder
          (\ _ v x -> S.insert v (quantVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` quantVars) x y
                 ((:~:) f) -> quantVars f)
          (\ _ -> S.empty)

-- |Find the free and quantified variables in a formula.
allVars :: FirstOrderFormula formula term v p f => formula -> S.Set v
allVars f =
    foldFirstOrder
          (\_ v x -> S.insert v (allVars x))
          (\ cm ->
               case cm of
                 BinOp x _ y -> (mappend `on` allVars) x y
                 (:~:) f' -> freeVars f')
          (\ pa -> case pa of
                     Equal t1 t2 -> S.union (allVarsOfTerm t1) (allVarsOfTerm t2)
                     NotEqual t1 t2 -> S.union (allVarsOfTerm t1) (allVarsOfTerm t2)
                     Constant _ -> S.empty
                     Apply _ ts -> S.unions (fmap allVarsOfTerm ts))
          f
    where
      allVarsOfTerm = foldTerm S.singleton (\ _ args -> S.unions (fmap allVarsOfTerm args))

-- | Universally quantify all free variables in the formula (Name comes from TPTP)
univquant_free_vars :: FirstOrderFormula formula term v p f => formula -> formula
univquant_free_vars cnf' =
    if S.null free then cnf' else foldr for_all cnf' (S.toList free)
    where free = freeVars cnf'

-- |Replace each free occurrence of variable old with term new.
substitute :: FirstOrderFormula formula term v p f => v -> term -> formula -> formula
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
                (\ pa -> case pa of
                           Equal t1 t2 -> (st t1) .=. (st t2)
                           NotEqual t1 t2 -> (st t1) .!=. (st t2)
                           Constant x -> pApp0 (fromBool x)
                           Apply p ts -> pApp p (map st ts))
      st t = foldTerm sv (\ func ts -> fApp func (map st ts)) t
      sv v = if v == old then new else var v

substitutePairs :: (FirstOrderFormula formula term v p f) => [(v, term)] -> formula -> formula
substitutePairs pairs formula = foldr (\ (old, new) f -> substitute old new f) formula pairs 

-- |Convert any instance of a first order logic expression to any other.
convertFOF :: forall formula1 term1 v1 p1 f1 formula2 term2 v2 p2 f2.
              (FirstOrderFormula formula1 term1 v1 p1 f1,
               FirstOrderFormula formula2 term2 v2 p2 f2) =>
              (v1 -> v2) -> (p1 -> p2) -> (f1 -> f2) -> formula1 -> formula2
convertFOF convertV convertP convertF formula =
    foldFirstOrder q c p formula
    where
      convert' = convertFOF convertV convertP convertF
      convertTerm' = convertTerm convertV convertF
      q x v f = quant x (convertV v) (convert' f)
      c (BinOp f1 op f2) = combine (BinOp (convert' f1) op (convert' f2))
      c ((:~:) f) = combine ((:~:) (convert' f))
      p (Equal t1 t2) = (convertTerm' t1) .=. (convertTerm' t2)
      p (NotEqual t1 t2) = (convertTerm' t1) .!=. (convertTerm' t2)
      p (Apply x ts) = pApp (convertP x) (map convertTerm' ts)
      p (Constant x) = pApp (fromBool x) []

-- |Names for for_all and exists inspired by the conventions of the
-- TPTP project.
(!) :: FirstOrderFormula formula term v p f => v -> formula -> formula
(!) = for_all
(?) :: FirstOrderFormula formula term v p f => v -> formula -> formula
(?) = exists

-- |Try to convert a first order logic formula to propositional.  This
-- will return Nothing if there are any quantifiers, or if it runs
-- into an atom that it is unable to convert.
toPropositional :: forall formula1 term v p f formula2 atom.
                   (FirstOrderFormula formula1 term v p f,
                    PropositionalFormula formula2 atom) =>
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
showFirstOrder :: forall formula term v p f. (FirstOrderFormula formula term v p f, Show v, Show p, Show f) => 
                  formula -> String
showFirstOrder formula =
    foldFirstOrder q c a formula
    where
      q All v f = "(for_all " ++ show v ++ " " ++ showFirstOrder f ++ ")"
      q Exists v f = "(exists " ++  show v ++ " " ++ showFirstOrder f ++ ")"
      c (BinOp f1 op f2) = "(" ++ parenForm f1 ++ " " ++ showCombine op ++ " " ++ parenForm f2 ++ ")"
      c ((:~:) f) = "((.~.) " ++ showFirstOrder f ++ ")"
      a :: Predicate p term -> String
      a (Equal t1 t2) =
          "(" ++ parenTerm t1 ++ " .=. " ++ parenTerm t2 ++ ")"
      a (NotEqual t1 t2) =
          "(" ++ parenTerm t1 ++ " .!=. " ++ parenTerm t2 ++ ")"
      a (Constant x) = "pApp' (Constant " ++ show x ++ ")"
      a (Apply p ts) = "(pApp" ++ show (length ts) ++ " (" ++ show p ++ ") (" ++ intercalate ") (" (map showTerm ts) ++ "))"
      parenForm x = "(" ++ showFirstOrder x ++ ")"
      parenTerm :: term -> String
      parenTerm x = "(" ++ showTerm x ++ ")"
      showCombine (:<=>:) = ".<=>."
      showCombine (:=>:) = ".=>."
      showCombine (:&:) = ".&."
      showCombine (:|:) = ".|."

prettyFirstOrder :: forall formula term v p f. (FirstOrderFormula formula term v p f) =>
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
                 ((:~:) f) -> text {-"¬"-} "~" <> prettyFirstOrder pv pp pf 5 f)
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

$(deriveSafeCopy 1 'base ''Quant)
$(deriveSafeCopy 1 'base ''Predicate)

$(deriveNewData [''Quant])
$(deriveNewData [''Predicate])
