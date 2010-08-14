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
    ( negationNormalForm
    , prenexNormalForm
    , disjunctiveNormalForm
    , skolemNormalForm
    , clausalNormalForm
    , implicativeNormalForm
    ) where

import Control.Monad.State (MonadPlus, msum, get, put)
import Data.Generics (Data, Typeable, listify)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic
import Logic.Monad (SkolemT, LogicState(..), newLogicState)

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
negationNormalForm = moveNotInwards . simplify

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
prenexNormalForm :: (FirstOrderLogic formula term v p f, Eq formula, Enum v) => formula -> formula
prenexNormalForm = moveQuantifiersOut . negationNormalForm

moveQuantifiersOut :: forall formula term v p f. (FirstOrderLogic formula term v p f, Eq formula, Enum v) =>
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
      -- doLHS :: formula -> BinOp -> formula -> formula
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
      -- doRHS :: formula -> BinOp -> formula -> formula
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
renameFreeVars :: forall formula term v p f. (FirstOrderLogic formula term v p f, Enum v) =>
                  S.Set v -> [v] -> formula -> ([v], formula)
renameFreeVars s vs f =
    (vs'', substitutePairs (zip vs (map var vs'')) f)
    where
      (vs'', _) = foldr (\ v (vs', s') ->
                             if S.member v s'
                             then let v' = findName s' v in (v' : vs', S.insert v' s')
                             else (v : vs', S.insert v s')) ([], s) vs
      findName :: S.Set v -> v -> v
      findName s' v = if S.member v s' then findName s' (succ v) else v
{-
      nextName :: String -> String
      nextName 
      nextName "x" = "y"
      nextName "y" = "z"
      nextName v =
          reverse (show (1 + read (if n == "" then "1" else n) :: Int) ++
                   {- (if a == "" then "x" else a) -} "x")
              where (n, _a) = break (not . isDigit) (reverse v)
-}

-- |Convert to Prenex Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
disjunctiveNormalForm :: (FirstOrderLogic formula term v p f, Eq formula, Enum v) => formula -> formula
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
skolemNormalForm :: (Monad m, FirstOrderLogic formula term v p f, Eq formula, Enum v) =>
                    formula -> SkolemT v term m formula
skolemNormalForm formula =
    put newLogicState >>  -- This is wrong, but it won't work without it :(
    skolemize (disjunctiveNormalForm formula)

skolemize :: forall m formula term v p f. (Monad m, FirstOrderLogic formula term v p f, Eq v) =>
              formula -> SkolemT v term m formula
skolemize =
    foldF n q b i p
    where
      n :: formula -> SkolemT v term m formula
      n s = skolemize s >>= \ (s' :: formula) -> return ((.~.) s')
      q All vs f =
          do logicState <- get
             -- Add these variables to the list while we are in the
             -- scope where they are universally quantified.
             put (logicState {univQuant = univQuant logicState ++ vs})
             result <- skolemize f >>= return . for_all vs
             put logicState
             return result
      q Exists vs f =
          do logicState <- get
             let skolemMap' = foldr (\ (v, c) -> Map.insert v (fApp (toSkolem c) (map var (univQuant logicState)))) (skolemMap logicState) (zip vs [skolemCount logicState ..])
             put (logicState { skolemCount = skolemCount logicState + length vs
                             , skolemMap = skolemMap' })
             skolemize f
      b s1 op s2 = skolemize s1 >>= \ s1' -> 
                   skolemize s2 >>= \ s2' -> return (binOp s1' op s2')
      i t1 op t2 =
          do t1' <- substituteCh t1
             t2' <- substituteCh t2
             return (infixPred t1' op t2')
      p pr ts = mapM substituteCh ts >>= return . pApp pr

      substituteCh :: term -> SkolemT v term m term
      substituteCh t =
          get >>= \ logicState ->
          foldT (\ v -> return (maybe (var v) id (Map.lookup v (skolemMap logicState))))
                (\ f ts -> mapM substituteCh ts >>= return . fApp f)
                t

-- |Convert to Skolem Normal Form and then remove the outermost
-- universal quantifiers.  Due to the nature of Skolem Normal Form,
-- this is actually all the remaining quantifiers, the result is
-- effectively a propositional logic formula.  The result is a
-- conjuncted list of clauses, where each clause is a list of
-- disjuncted literals:
-- @@
--   [[a, ~b], [c, ~d]] <-> ((a | ~b) & (c | ~d))
-- @@
clausalNormalForm :: (Monad m, FirstOrderLogic formula term v p f, Eq formula, Enum v) =>
                     formula -> SkolemT v term m [[formula]]
clausalNormalForm f = skolemNormalForm f >>= return . clausal . removeUniversal

clausal :: forall formula term v p f. (FirstOrderLogic formula term v p f, Eq formula {-, Pretty v, Pretty p, Pretty f-}) =>
           formula -> [[formula]]
clausal =
    filter (not . any isTrue) . map doClause . flatten
    where
      flatten f =
          foldF (\ _ -> [[f]])
                (\ _ _ f' -> flatten f')
                (\ f1 op f2 -> case op of
                                 (:&:) -> flatten f1 ++ flatten f2
                                 (:|:) -> [flatten' f1 ++ flatten' f2]
                                 _ -> e0)
                (\ _ _ _ -> [[f]])
                (\ _ _ -> [[f]])
                f
      flatten' :: formula -> [formula]
      flatten' f =
          foldF (\ _ -> [f])
                (\ _ _ _ -> [f])
                (\ f1 op f2 -> case op of
                                 (:|:) -> flatten' f1 ++ flatten' f2
                                 _ -> e0)
                (\ _ _ _ -> [f])
                (\ _ _ -> [f])
                f
      doClause fs = filter (not . isFalse) fs
      isFalse f = foldF isTrue e3 e3 e3 (\ p _ -> p == fromBool False) f where e3 _ _ _ = error ("clausal: " {- ++ show (prettyForm 0 f) -})
      isTrue f = foldF isFalse e3 e3 e3 (\ p _ -> p == fromBool True) f where e3 _ _ _ = error ("clausal: "  {- ++ show (prettyForm 0 f) -})
      e0 = error "clausal"

-- |Take the clause normal form, and turn it into implicative form,
-- where each clauses becomes an (LHS, RHS) pair with the negated
-- literals on the LHS and the non-negated literals on the RHS:
-- @
--   (a | ~b | c | ~d) becomes (b & d) => (a | c)
--   (~b | ~d) | (a | c)
--   ~~(~b | ~d) | (a | c)
--   ~(b & d) | (a | c)
-- @
-- If there are skolem functions on the RHS, split the formula using
-- this identity:
-- @
--   (a | b | c) => (d & e & f)
-- @
-- becomes
-- @
--    a | b | c => d
--    a | b | c => e
--    a | b | c => f
-- @
implicativeNormalForm :: forall m formula term v p f. 
                         (Monad m, FirstOrderLogic formula term v p f, Eq formula, Data formula, Typeable f, Enum v) =>
                         formula -> SkolemT v term m [([formula], [formula])]
implicativeNormalForm formula =
    clausalNormalForm formula >>= return . concatMap split . map (imply . foldl collect ([], []))
    where
      collect :: ([formula], [formula]) -> formula -> ([formula], [formula])
      collect (n, p) f =
          foldF (\ f' -> (f' : n, p))
                (\ _ _ _ -> error "collect 1")
                (\ _ _ _ -> error "collect 2")
                (\ _ _ _ -> (n, f : p))
                (\ _ _ -> (n, f : p))
                f
      imply :: ([formula], [formula]) -> ([formula], [formula])
      imply (n, p) = (reverse n, reverse p)
      split :: ([formula], [formula]) -> [([formula], [formula])]
      split (lhs, rhs) =
          if any isJust (map fromSkolem (gFind rhs :: [f]))
          then map (\ x -> (lhs, [x])) rhs
          else [(lhs, rhs)]

removeUniversal :: FirstOrderLogic formula term v p f => formula -> formula
removeUniversal formula =
    foldF (.~.) removeAll binOp infixPred pApp formula
    where
      removeAll All _ f = removeUniversal f
      removeAll Exists vs f = exists vs (removeUniversal f)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
