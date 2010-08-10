{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
-- |A series of transformations to convert first order logic formulas
-- into (ultimately) Clause Normal Form.
-- 
-- @
-- 1st order formula:
--   ∀Y (∀X (taller(Y,X) | wise(X)) => wise(Y))
-- 
-- Simplify
--   ∀Y (~∀X (taller(Y,X) | wise(X)) | wise(Y))
-- 
-- Move negations in - Negation Normal Form
--   ∀Y (∃X (~taller(Y,X) & ~wise(X)) | wise(Y))
-- 
-- Move quantifiers out - Prenex Normal Form
--   ∀Y (∃X ((~taller(Y,X) & ~wise(X)) | wise(Y)))
-- 
-- Distribute disjunctions
--   ∀Y ∃X ((~taller(Y,X) | wise(Y)) & (~wise(X) | wise(Y)))
-- 
-- Skolemize  - Skolem Normal Form
--   ∀Y (~taller(Y,x(Y)) | wise(Y)) & (~wise(x(Y)) | wise(Y))
-- 
-- Convert to CNF
--   { ~taller(Y,x(Y)) | wise(Y),
--     ~wise(x(Y)) | wise(Y) } 
-- @
-- 
module Logic.NormalForm
    ( simplify
    , negationNormalForm
    , prenexNormalForm
    , disjunctiveNormalForm
    , skolemNormalForm
    , clausalNormalForm
    , cnf
    -- , cnfTraced
    , implicativeNormalForm
    , toINF
    , moveQuantifiersOut
    , skolemize
    , eliminateImplication
    , moveNotInwards
    , distributeDisjuncts
    ) where

import Data.Char (isDigit)
import qualified Data.Map as Map
import Data.String (IsString(..))
import qualified Data.Set as S
--import Debug.Trace
import Logic.FirstOrder
import Logic.Implicative (Implicative(..))
import Logic.Logic

-- |Simplify:
-- 
-- @
--  P <~> Q     (P | Q) & (~P | ~Q)
--  P <=> Q     (P => Q) & (Q => P)
--  P => Q      ~P | Q
-- @
-- 
simplify :: FirstOrderLogic formula term v p f => formula -> formula
simplify = eliminateImplication
{-
simplify :: FirstOrderLogic formula term v p f => formula -> formula
simplify =
    foldF n q b i a
    where
      q All vs f = for_all vs (simplify f)
      q Exists vs f = exists vs (simplify f)
      b :: FirstOrderLogic formula term v p f => formula -> BinOp -> formula -> formula
      b f1 (:&:) f2 = simplify f1 .&. simplify f2
      b f1 (:|:) f2 = simplify f1 .|. simplify f2
      b f1 (:=>:) f2 = ((.~.) (simplify f1)) .|. simplify f2
      b f1 (:<=>:) f2 = simplify ((f1 .=>. f2) .&. (f2 .=>. f1))
      n f = (.~.) (simplify f)
      i t1 (:=:) t2 = t1 .=. t2
      i t1 (:!=:) t2 = t1 .!=. t2
      a p ts = pApp p ts
-}

{-- 
   Invariants:
   P => Q           becomes       (NOT P) OR Q
   P <=> Q          becomes       ((NOT P) OR Q) AND ((NOT Q) OR P)
 -}
eliminateImplication :: FirstOrderLogic formula term v p f =>
                        formula -> formula
eliminateImplication =
    foldF n q b infixPred pApp
    where
      n f = (.~.) (eliminateImplication f)
      q vs op f = quant vs op (eliminateImplication f)
      b f1 op f2 =
          case op of
            (:=>:) -> ((.~.) f1') .|. f2'
            (:<=>:) -> eliminateImplication ((f1 .=>. f2) .&. (f2 .=>. f1))
            _ -> binOp f1' op f2'
          where
            f1' = eliminateImplication f1
            f2' = eliminateImplication f2

-- |Simplify and then move negations inwards:
-- 
-- @
-- Formula      Rewrites to
-- ~∀X P        ∃X ~P
-- ~∃X P        ∀X ~P
-- ~(P & Q)     (~P | ~Q)
-- ~(P | Q)     (~P & ~Q)
-- ~~P  P
-- @
-- 
negationNormalForm :: FirstOrderLogic formula term v p f => formula -> formula
negationNormalForm = moveNegationsIn . simplify

moveNegationsIn :: FirstOrderLogic formula term v p f => formula -> formula
moveNegationsIn = moveNotInwards
{-
moveNegationsIn =
    foldF n q b i a
    where
      n f = doNegation f
      q All vs f = for_all vs (moveNegationsIn f)
      q Exists vs f = exists vs (moveNegationsIn f)
      b f1 (:&:) f2 = moveNegationsIn f1 .&. moveNegationsIn f2
      b f1 (:|:) f2 = moveNegationsIn f1 .|. moveNegationsIn f2
      -- These are already gone
      b _ op _ = error $ "moveNegationsIn: Unexpected BinOp " ++ show op
      -- b f1 op f2 = binOp f1 op f2
      i = infixPred
      a p ts = pApp p ts
      -- Helper function for moveNegationsIn, for already negated formulae
      doNegation :: FirstOrderLogic formula term v p f => formula -> formula
      doNegation =
          foldF n' q' b' i' a'
          where
            n' f = moveNegationsIn f -- double negation
            q' All vs f = exists vs (moveNegationsIn ((.~.) f))
            q' Exists vs f = for_all vs (moveNegationsIn ((.~.) f))
            b' f1 (:|:) f2 = moveNegationsIn ((.~.) f1) .&. moveNegationsIn ((.~.) f2)
            b' f1 (:&:) f2 = moveNegationsIn ((.~.) f1) .|. moveNegationsIn ((.~.) f2)
            b' _ op _ = error $ "moveNegationsIn: Unexpected BinOp " ++ show op
            i' t1 op t2 = (.~.) (infixPred t1 op t2)
            a' p ts = (.~.) (pApp p ts)
-}

{--
   Invariants:
   NOT (P OR Q)      becomes     (NOT P) AND (NOT Q)
   NOT (P AND Q)     becomes     (NOT P) OR (NOT Q)
   NOT (ForAll x P)  becomes     Exists x (NOT P)
   NOT (Exists x P)  becomes     ForAll x (NOT P)
   NOT (NOT P)       becomes     P
 -}
moveNotInwards :: forall formula term v p f. FirstOrderLogic formula term v p f =>
                  formula -> formula
moveNotInwards formula =
    foldF n q b infixPred pApp formula
    where
      n f = foldF moveNotInwards
                  (\ op vs f' -> 
                       case op of
                         Exists -> for_all vs (moveNotInwards ((.~.) f'))
                         All -> exists vs (moveNotInwards ((.~.) f')))
                  (\ f1 op f2 ->
                       case op of
                         (:&:) -> moveNotInwards (((.~.) f1) .|. ((.~.) f2))
                         (:|:) -> moveNotInwards (((.~.) f1) .&. ((.~.) f2))
                         _ -> (.~.) (binOp (moveNotInwards f1) op (moveNotInwards f2)))
                  (\ t1 op t2 -> (.~.) (infixPred t1 op t2))
                  (\ p ts -> (.~.) (pApp p ts))
                  f
      q op vs f = quant op vs (moveNotInwards f)
      b f1 op f2 = binOp (moveNotInwards f1) op (moveNotInwards f2)

-- |Convert to Negation Normal Form and then move quantifiers outwards:
-- 
-- @
--  Formula     Rewrites to
--  ∀X P & Q    ∀X (P & Q)
--  ∃X P & Q    ∃X (P & Q)
--  Q & ∀X P    ∀X (Q & P)
--  Q & ∃X P    ∃X (Q & P)
--  ∀X P | Q    ∀X (P | Q)
--  ∃X P | Q    ∃X (P | Q)
--  Q | ∀X P    ∀X (Q | P)
--  Q | ∃XP     ∃X (Q | P)
-- @
-- 
-- We also need to do some variable renaming here, so that in an
-- example like @&#8704;X P & Q -> &#8704;X (P & Q)@ there are no references to X
-- in Q.  We choose to examine Q and if X appears there, find another
-- variable which does not appear and change occurrences of X in P to
-- this new variable.  We could instead modify Q, but that looks
-- slightly more tedious.
prenexNormalForm :: (FirstOrderLogic formula term v p f, Eq formula) => formula -> formula
prenexNormalForm = moveQuantifiersOut . negationNormalForm

moveQuantifiersOut :: forall formula term v p f. (FirstOrderLogic formula term v p f, Eq formula) =>
                      formula -> formula
moveQuantifiersOut formula =
    foldF n q b i a formula
    where
      -- We don't need to do this because we've already moved the
      -- negations inside all the quantifiers
      n = (.~.)
      q op vs f = quant op vs (moveQuantifiersOut f)
      b f1 op f2 = doLHS (moveQuantifiersOut f1) op (moveQuantifiersOut f2)
      i t1 op t2 = infixPred t1 op t2
      a p ts = pApp p ts
      -- We found :&: or :|: above, look for quantifiers to move out, first examine f1
      -- f1=(∀X P), f2=Q
      doLHS :: formula -> BinOp -> formula -> formula
      doLHS f1 op f2 =
          foldF n' q' b' i' a' f1
          where
            n' _ = doRHS f1 op f2
            -- We see (∃X f(x)) | f2, which we want to change to ∃x
            -- (f(x) | f2).  The problem we have is that there could
            -- be free occurrences of x in f2 (probably quantified in
            -- an expression we have already recursed into), so moving
            -- the quantifier changes the meaning of the expression.
            -- To avoid this we must find a replacement for x which is
            -- not free in f2, perhaps y: ∃y (f(y) | f2).
            q' qop vs f =
                let (vs', f') = renameFreeVars (freeVars f2) vs f in
                quant qop vs' (moveQuantifiersOut (doBinOp f' op f2))
            b' _ _ _ = doRHS f1 op f2
            i' _ _ _ = doRHS f1 op f2
            a' _ _ = doRHS f1 op f2
      -- We reached a point where f1 was not a quantifier, try f2
      doRHS :: formula -> BinOp -> formula -> formula
      doRHS f1 op f2 =
          foldF n' q' b' i' a' f2
          where
            n' _ = doBinOp f1 op f2
            q' qop vs f =
                let (vs', f') = renameFreeVars (freeVars f1) vs f in
                quant qop vs' (moveQuantifiersOut (doBinOp f1 op f'))
            b' _ _ _ = doBinOp f1 op f2
            i' _ _ _ = doBinOp f1 op f2
            a' _ _ = doBinOp f1 op f2
      -- doBinOp :: formula -> BinOp -> formula -> formula
      doBinOp f1 (:&:) f2 = f1 .&. f2
      doBinOp f1 (:|:) f2 = f1 .|. f2
      doBinOp _ op _ = error $ "moveQuantifierOut: unexpected BinOp " ++ show op

-- |Find new variables that are not in the set and substitute free
-- occurrences in the formula.
renameFreeVars :: forall formula term v p f. FirstOrderLogic formula term v p f =>
                  S.Set v -> [v] -> formula -> ([v], formula)
renameFreeVars s vs f =
    (vs'', substitutePairs (zip vs (map var vs'')) f)
    where
      (vs'', _) = foldr (\ v (vs', s') ->
                             if S.member v s'
                             then let v' = fromString (findName s' "x") in (v' : vs', S.insert v' s')
                             else (v : vs', S.insert v s')) ([], s) vs
      findName :: S.Set v -> String -> String
      findName s' v = if S.member (fromString v) s' then findName s' (nextName v) else v
      nextName :: String -> String
      nextName "x" = "y"
      nextName "y" = "z"
      nextName v =
          reverse (show (1 + read (if n == "" then "1" else n) :: Int) ++
                   {- (if a == "" then "x" else a) -} "x")
              where (n, _a) = break (not . isDigit) (reverse v)

-- |Convert to Prenex Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
disjunctiveNormalForm :: (FirstOrderLogic formula term v p f, Eq formula) => formula -> formula
disjunctiveNormalForm = distributeDisjuncts . prenexNormalForm

distributeDisjuncts :: FirstOrderLogic formula term v p f => formula -> formula
distributeDisjuncts =
    foldF n q b i a
    where
      n = (.~.)
      q All vs x = for_all vs (distributeDisjuncts x)
      q Exists vs x = exists vs (distributeDisjuncts x)
      b f1 (:|:) f2 = doRHS (distributeDisjuncts f1) (distributeDisjuncts f2)
      b f1 (:&:) f2 = distributeDisjuncts f1 .&. distributeDisjuncts f2
      b f1 op f2 = binOp (distributeDisjuncts f1) op (distributeDisjuncts f2)
      i = infixPred
      a = pApp
      -- Helper function once we've seen a disjunction.  Note that it does not call itself.
      doRHS f1 f2 =
          foldF n' q' b' i' a' f2
          where
            n' _ = doLHS f1 f2
            -- Quick simplification, but assumes Eq formula: (p | q) & p -> p
            -- b' f3 (:&:) f4 | f1 == f3 || f1 == f4 = distributeDisjuncts f1
            b' f3 (:&:) f4 = distributeDisjuncts (distributeDisjuncts (f1 .|. f3) .&. distributeDisjuncts (f1 .|. f4))
            b' _ _ _ = doLHS f1 f2
            q' _ _ _ = doLHS f1 f2
            i' _ _ _ = doLHS f1 f2
            a' _ _ = doLHS f1 f2
      doLHS f1 f2 =
          foldF n' q' b' i' a' f1
          where
            n' _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            q' _ _ _ =  distributeDisjuncts f1 .|. distributeDisjuncts f2
            -- Quick simplification, but assumes Eq formula: p & (p | q) -> p
            -- b' f3 (:&:) f4 | f2 == f3 || f2 == f4 = distributeDisjuncts f2
            b' f3 (:&:) f4 = distributeDisjuncts (distributeDisjuncts (f3 .|. f2) .&. distributeDisjuncts (f4 .|. f2))
            b' _ _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            i' _ _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            a' _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2

-- |Convert to Disjunctive Normal Form and then Skolemize.  This means
-- removing the existential quantifiers and replacing the variables
-- they quantify with skolem functions (and constants, which are
-- functions of zero variables.)  The Skolem functions are new
-- functions applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolemNormalForm :: (FirstOrderLogic formula term v p f, Eq formula) =>
                    formula -> formula
skolemNormalForm = skolemize . disjunctiveNormalForm

skolemize :: forall formula term v p f. (FirstOrderLogic formula term v p f, Eq v) =>
             formula -> formula
skolemize =
    skolemize' 1 [] Map.empty
    where
      skolemize' :: FirstOrderLogic formula term v p f => Int -> [v] -> Map.Map v term -> formula -> formula
      skolemize' cnt univ skmap formula =
          foldF n q b i p formula
          where
            n s = (.~.) (skolemize' cnt univ skmap s)
            q All vs = skolemize' cnt (univ ++ vs) skmap
            q Exists vs = skolemize' (cnt + length vs) univ (skolemCh cnt vs univ skmap)
            b s1 op s2 = binOp (skolemize' cnt univ skmap s1) op (skolemize' cnt univ skmap s2)
            i t1 op t2 = infixPred (substituteCh skmap t1) op (substituteCh skmap t2)
            p pr ts = pApp pr (map (substituteCh skmap) ts)

      skolemCh i (v:vs) u skmap = skolemCh (i+1) vs u (Map.insert v (fApp (toSkolem i) (map var u)) skmap)
      skolemCh _i [] _u skmap = skmap

      substituteCh skmap t =
          foldT (\ v -> maybe (var v) id (Map.lookup v skmap))
                (\ f ts -> fApp f (map (substituteCh skmap) ts))
                t

-- |Convert to Skolem Normal Form and then remove the outermost
-- universal quantifiers.  Due to the nature of Skolem Normal Form,
-- this is actually all the remaining quantifiers, the result is
-- effectively a propositional logic formula.
clausalNormalForm :: (FirstOrderLogic formula term v p f, Eq formula) =>
                     formula -> formula
clausalNormalForm = {- removeUniversal . -} skolemNormalForm

toINF :: forall inf formula term v p f. Implicative inf formula term v p f => formula -> [inf]
toINF formula = toImplicative formula :: [inf]

implicativeNormalForm :: forall inf formula term v p f. 
                         Implicative inf formula term v p f =>
                         formula -> formula
implicativeNormalForm formula =
    conjunctList . map fromImplicative $ (toImplicative formula :: [inf])
    where
      conjunctList (x : xs) = foldl (.&.) x xs
      conjunctList [] = pApp (fromBool True) []

removeUniversal :: FirstOrderLogic formula term v p f => formula -> formula
removeUniversal formula =
    foldF (.~.) removeAll binOp infixPred pApp formula
    where
      removeAll All _ f = removeUniversal f
      removeAll Exists vs f = exists vs (removeUniversal f)

-- |Nickname for clausalNormalForm.
cnf :: (FirstOrderLogic formula term v p f, Eq formula) =>
       formula -> formula
cnf = clausalNormalForm

-- |Nickname for clausalNormalForm.
{-
cnfTraced :: (FirstOrderLogic formula term v p f, Eq formula, Show formula) => formula -> formula
cnfTraced =
    t6 . removeUniversal . t5 . skolemize . t4 . distributeDisjuncts . t3 . moveQuantifiersOut . t2 . moveNegationsIn . simplify . t1
    where
      t1 x = trace ("\ninput: " ++ show x) x
      t2 x = trace ("NNF:   " ++ show x) x
      t3 x = trace ("PNF:   " ++ show x) x
      t4 x = trace ("DNF:   " ++ show x) x
      t5 x = trace ("SNF:   " ++ show x) x
      t6 x = trace ("CNF:   " ++ show x) x
-}
