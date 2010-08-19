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
    , uniqueQuantifiedVariables
    , prenexNormalForm
    , disjunctiveNormalForm
    , skolemNormalForm
    , clausalNormalForm
    , cnfTrace
    , implicativeNormalForm
    ) where

import Control.Monad.State (MonadPlus, msum, get, put, modify)
import Data.Generics (Data, Typeable, listify)
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic
import Logic.Monad (NormalT, LogicState(..))
import Text.PrettyPrint (hcat, vcat, text, nest, ($$), brackets, render)

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
      q op v f = quant op v (eliminateImplication f)
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
negationNormalForm :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
negationNormalForm f =  uniqueQuantifiedVariables (simplify f) >>= return . moveNotInwards

{--
   Invariants:
   NOT (P OR Q)      becomes     (NOT P) AND (NOT Q)
   NOT (P AND Q)     becomes     (NOT P) OR (NOT Q)
   NOT (ForAll x P)  becomes     Exists x (NOT P)
   NOT (Exists x P)  becomes     ForAll x (NOT P)
   NOT (NOT P)       becomes     P
 -}
moveNotInwards :: FirstOrderLogic formula term v p f =>
                  formula -> formula
moveNotInwards formula =
    foldF n q b infixPred pApp formula
    where
      n f = foldF moveNotInwards
                  (\ op v f' -> 
                       case op of
                         Exists -> for_all v (moveNotInwards ((.~.) f'))
                         All -> exists v (moveNotInwards ((.~.) f')))
                  (\ f1 op f2 ->
                       case op of
                         (:&:) -> moveNotInwards (((.~.) f1) .|. ((.~.) f2))
                         (:|:) -> moveNotInwards (((.~.) f1) .&. ((.~.) f2))
                         _ -> (.~.) (binOp (moveNotInwards f1) op (moveNotInwards f2)))
                  (\ t1 op t2 -> (.~.) (infixPred t1 op t2))
                  (\ p ts -> (.~.) (pApp p ts))
                  f
      q op v f = quant op v (moveNotInwards f)
      b f1 op f2 = binOp (moveNotInwards f1) op (moveNotInwards f2)

prenexNormalForm :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
prenexNormalForm formula = negationNormalForm formula >>= return . moveQuantifiersOut

uniqueQuantifiedVariables :: forall m formula term v p f. (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
uniqueQuantifiedVariables formula =
    modify (\ s -> s {varNames = S.empty}) >>
    rename formula
    where
      -- Choose unique names for the quantified variables
      rename :: formula -> NormalT v term m formula
      rename =
          foldF (\ f -> rename f >>= return . (.~.))
                (\ op v f ->
                     rename f >>= \ f' ->
                     chooseName v >>= \ v' ->
                     return . quant op v' $ renameFree (v, v') f')
                (\ f1 op f2 -> rename f1 >>= \ f1' -> rename f2 >>= \ f2' ->
                               return $ binOp f1' op f2')
                (\ t1 op t2 -> return $ infixPred t1 op t2)
                (\ p ts -> return $ pApp p ts)
      -- Choose a new name for v
      chooseName :: v -> NormalT v term m v
      chooseName v =
          do state <- get
             let used = varNames state
                 v' = head (dropWhile (`S.member` used) (iterate succ v))
             put (state {varNames = S.insert v' used})
             return v'
      renameFree :: (v, v) -> formula -> formula
      renameFree (v, v') f = substitute v (var v') f

-- |Convert from Negation Normal Form to Prenex Normal Form using
-- 
-- @
--  Formula            Rewrites to
--  (1) ∀x F[x] & G        ∀x    (F[x] & G)
--  (2) ∀x F[x] & ∀x G[x]  ∀x ∀x (F[x] & G[x])
--  (3) ∃x F[x] & G        ∃x    (F[x] & G)
--  (4) ∃x F[x] & ∃x G[x]  ∃x Yz (F[x] & G[z]) -- rename
-- 
--  (5) ∀x F[x] | G        ∀x    (F[x] | G)
--  (6) ∀x F[x] | ∀x G[x]  ∀x ∀z (F[x] | G[z]) -- rename
--  (7) ∃x F[x] | G        ∃x    (F[x] | G)
--  (8) ∃x F[x] | ∃x G[x]  ∃x Yx (F[x] | G[x])
-- @
-- 
-- We also need to do some variable renaming here, so that in an
-- example like @&#8704;X P & Q -> &#8704;X (P & Q)@ there are no references to X
-- in Q.  We choose to examine Q and if X appears there, find another
-- variable which does not appear and change occurrences of X in P to
-- this new variable.  We could instead modify Q, but that looks
-- slightly more tedious.
moveQuantifiersOut :: forall formula term v p f. FirstOrderLogic formula term v p f =>
                      formula -> formula
moveQuantifiersOut =
    merge . collect
    where
      -- Split the quantifiers out of the formulas
      collect :: formula -> ([(Quant, v)], formula)
      collect =
          foldF (\ f -> ([], (.~.) f))
                (\ op v f ->
                     let (pairs, f') = collect f in
                     ((op, v) : pairs, f'))
                (\ lf op rf ->
                     let (lpairs, lf') = collect lf
                         (rpairs, rf') = collect rf in
                     prenex (lpairs, lf') op (rpairs, rf'))
                (\ t1 op t2 -> ([], infixPred t1 op t2))
                (\ p ts -> ([], pApp p ts))
      prenex :: ([(Quant, v)], formula) -> BinOp -> ([(Quant, v)], formula) -> ([(Quant, v)], formula)
      prenex (lqs, lf) op (rqs, rf) = (lqs ++ rqs, binOp lf op rf)

      merge :: ([(Quant, v)], formula) -> formula
      merge ([], f) = f
      -- Note that the resulting variable lists will all be singletons.
      merge ((q, v) : qs, f) = quant q v (merge (qs, f))

-- |Convert to Prenex Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
disjunctiveNormalForm :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
disjunctiveNormalForm formula = prenexNormalForm formula >>= return . distributeDisjuncts

distributeDisjuncts :: FirstOrderLogic formula term v p f => formula -> formula
distributeDisjuncts =
    foldF n q b i a
    where
      n = (.~.)
      q All v x = for_all v (distributeDisjuncts x)
      q Exists v x = exists v (distributeDisjuncts x)
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
skolemNormalForm :: forall m formula term v p f. (Monad m, FirstOrderLogic formula term v p f) =>
                    formula -> NormalT v term m formula
skolemNormalForm formula =
    do dnf <- disjunctiveNormalForm formula
       result1 <- skolemize dnf
       -- state <- get
       -- put (state { skolemCount = 1, skolemMap = Map.empty, univQuant = [] })
       -- result2 <- skolemize dnf
       -- put state
       {- (if result1 /= result2
          then trace ("\nSkolemization discrepancy:\n result1=" ++ show (prettyForm 0 result1) ++ "\n result2=" ++ show (prettyForm 0 result2)) result1
          else result1) -}
       return result1

skolemize :: forall m formula term v p f. (Monad m, FirstOrderLogic formula term v p f) =>
             formula -> NormalT v term m formula
skolemize =
    foldF n q b i p
    where
      n :: formula -> NormalT v term m formula
      n s = skolemize s >>= \ (s' :: formula) -> return ((.~.) s')
      q All v f =
          do logicState <- get
             -- Add these variables to the list while we are in the
             -- scope where they are universally quantified.  (FIXME:
             -- it is not necessary to add it to the end, but when
             -- this is changed the test cases need updating.)
             put (logicState {univQuant = univQuant logicState ++ [v]})
             result <- skolemize f >>= return . for_all v
             put logicState
             return result
      q Exists v f =
          do logicState <- get
             let skolemMap' = Map.insert v (fApp (toSkolem (skolemCount logicState)) (map var (univQuant logicState))) (skolemMap logicState)
             put (logicState { skolemCount = skolemCount logicState + 1
                             , skolemMap = skolemMap' })
             skolemize f
      b s1 op s2 = skolemize s1 >>= \ s1' -> 
                   skolemize s2 >>= \ s2' -> return (binOp s1' op s2')
      i t1 op t2 =
          do t1' <- substituteCh t1
             t2' <- substituteCh t2
             return (infixPred t1' op t2')
      p pr ts = mapM substituteCh ts >>= return . pApp pr

      substituteCh :: term -> NormalT v term m term
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
clausalNormalForm :: (Monad m, FirstOrderLogic formula term v p f) =>
                     formula -> NormalT v term m [[formula]]
clausalNormalForm f = skolemNormalForm f >>= return . clausal . removeUniversal

clausal :: FirstOrderLogic formula term v p f =>
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
      -- flatten' :: formula -> [formula]
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

cnfTrace :: (Monad m, FirstOrderLogic formula term v p f, Pretty v, Pretty p, Pretty f) =>
            formula -> NormalT v term m String
cnfTrace f =
    do simplified <- uniqueQuantifiedVariables (simplify f)
       nnf <- negationNormalForm simplified
       pnf <- prenexNormalForm nnf
       dnf <- disjunctiveNormalForm pnf
       snf <- skolemNormalForm dnf
       cnf <- clausalNormalForm snf
       return . render . vcat $
                  [text "Original:" $$ nest 2 (prettyForm 0 f),
                   text "Simplified:" $$ nest 2 (prettyForm 0 simplified),
                   text "Negation Normal Form:" $$ nest 2 (prettyForm 0 nnf),
                   text "Prenex Normal Form:" $$ nest 2 (prettyForm 0 pnf),
                   text "Disjunctive Normal Form:" $$ nest 2 (prettyForm 0 dnf),
                   text "Skolem Normal Form:" $$ nest 2 (prettyForm 0 snf),
                   text "Clause Normal Form:" $$ vcat (map (nest 2 . brackets . hcat . intersperse (text ", ") . map (nest 2 . brackets . prettyForm 0)) cnf)]

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
                         (Monad m, FirstOrderLogic formula term v p f, Data formula) =>
                         formula -> NormalT v term m [([formula], [formula])]
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
      removeAll Exists v f = exists v (removeUniversal f)

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
