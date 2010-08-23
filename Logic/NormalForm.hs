{-# LANGUAGE FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, UndecidableInstances #-}
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
    , skolemNormalForm
    , clauseNormalForm
    , trivial
    , cnfTrace
    , implicativeNormalForm
    ) where

import Control.Monad.State (MonadPlus, msum, get, put)
import Data.Generics (Data, Typeable, listify)
import Data.List (intersperse)
import Data.Maybe (isJust)
import Logic.Clause (Literal(..))
import Logic.FirstOrder
import Logic.Logic
import Logic.Monad (NormalT, LogicState(..))
import qualified Logic.Set as S
import Text.PrettyPrint (hcat, vcat, text, nest, ($$), brackets, render)

-- |Do a bottom-up recursion to simplify a formula.
simplify :: FirstOrderLogic formula term v p f => formula -> formula
simplify fm =
    foldF (\ op v p -> simplify1 (quant op v (simplify p)))
          (\ cm -> case cm of
                     (:~:) p -> simplify1 ((.~.) (simplify p))
                     BinOp p op q -> simplify1 (combine (BinOp (simplify p) op (simplify q))))
          (\ _ _ -> simplify1 fm)
          fm

-- |Do one step of simplify for propositional formulas:
-- Perform the following transformations everywhere, plus any
-- commuted versions for &, |, and <=>.
-- 
-- @
--  ~False      -> True
--  ~True       -> False
--  True & P    -> P
--  False & P   -> False
--  True | P    -> True
--  False | P   -> P
--  True => P   -> P
--  False => P  -> True
--  P => True   -> P
--  P => False  -> True
--  True <=> P  -> P
--  False <=> P -> ~P
-- @
-- 
psimplify1 :: forall formula term v p f. FirstOrderLogic formula term v p f => formula -> formula
psimplify1 fm =
    foldF (\ _ _ _ -> fm) simplifyCombine (\ _ _ -> fm) fm
    where
      simplifyCombine ((:~:) f) = foldF (\ _ _ _ -> fm) simplifyNotCombine simplifyNotPred f
      simplifyCombine (BinOp l op r) =
          case (pBool l, op, pBool r) of
            (Just True,  (:&:), _)            -> r
            (Just False, (:&:), _)            -> false
            (_,          (:&:), Just True)    -> l
            (_,          (:&:), Just False)   -> false
            (Just True,  (:|:), _)            -> true
            (Just False, (:|:), _)            -> r
            (_,          (:|:), Just True)    -> true
            (_,          (:|:), Just False)   -> l
            (Just True,  (:=>:), _)           -> r
            (Just False, (:=>:), _)           -> true
            (_,          (:=>:), Just True)   -> true
            (_,          (:=>:), Just False)  -> (.~.) l
            (Just True,  (:<=>:), _)          -> r
            (Just False, (:<=>:), _)          -> (.~.) r
            (_,          (:<=>:), Just True)  -> l
            (_,          (:<=>:), Just False) -> (.~.) l
            _                                 -> fm
      simplifyNotCombine ((:~:) f) = f
      simplifyNotCombine _ = fm
      simplifyNotPred pr ts
          | pr == fromBool False = pApp (fromBool True) ts
          | pr == fromBool True = pApp (fromBool False) ts
          | True = (.~.) (pApp pr ts)
      -- Return a Maybe Bool depending upon whether a formula is true,
      -- false, or something else.
      pBool :: formula -> Maybe Bool
      pBool = foldF (\ _ _ _ -> Nothing) (\ _ -> Nothing)
                    (\ pr _ts -> if pr == fromBool True
                                 then Just True
                                 else if pr == fromBool False
                                      then Just False
                                      else Nothing)
      true = pApp (fromBool True) []
      false = pApp (fromBool False) []
      
-- |Extend psimplify1 to handle quantifiers.  Any quantifier which has
-- no corresponding free occurrences of the quantified variable is
-- eliminated.
simplify1 :: FirstOrderLogic formula term v p f => formula -> formula
simplify1 fm =
    foldF (\ _ v p -> if S.member v (freeVars p) then fm else p)
          (\ _ -> psimplify1 fm)
          (\ _ _ -> psimplify1 fm)
          fm

-- | Simplify and recursively apply nnf.
negationNormalForm :: FirstOrderLogic formula term v p f => formula -> formula
negationNormalForm = nnf . simplify

-- |Eliminate => and <=> and move negations inwards:
-- 
-- @
-- Formula      Rewrites to
--  P => Q      ~P | Q
--  P <=> Q     (P & Q) | (~P & ~Q)
-- ~∀X P        ∃X ~P
-- ~∃X P        ∀X ~P
-- ~(P & Q)     (~P | ~Q)
-- ~(P | Q)     (~P & ~Q)
-- ~~P  P
-- @
-- 
nnf :: FirstOrderLogic formula term v p f => formula -> formula
nnf fm =
    foldF nnfQuant nnfCombine (\ _ _ -> fm) fm
    where
      nnfQuant op v p = quant op v (nnf p)
      nnfCombine ((:~:) p) = foldF nnfNotQuant nnfNotCombine (\ _ _ -> fm) p
      nnfCombine (BinOp p (:=>:) q) = nnf ((.~.) p) .|. (nnf q)
      nnfCombine (BinOp p (:<=>:) q) =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfCombine (BinOp p (:&:) q) = nnf p .&. nnf q
      nnfCombine (BinOp p (:|:) q) = nnf p .|. nnf q
      nnfNotQuant All v p = exists v (nnf ((.~.) p))
      nnfNotQuant Exists v p = for_all v (nnf ((.~.) p))
      nnfNotCombine ((:~:) p) = nnf p
      nnfNotCombine (BinOp p (:&:) q) = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:|:) q) = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:=>:) q) = nnf p .&. nnf ((.~.) q)
      nnfNotCombine (BinOp p (:<=>:) q) = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

-- |Convert to Prenex normal form, with all quantifiers at the left.
prenexNormalForm :: (FirstOrderLogic formula term v p f) => formula -> formula
prenexNormalForm = prenex . negationNormalForm

-- |Recursivly apply pullQuants anywhere a quantifier might not be
-- leftmost.
prenex :: (FirstOrderLogic formula term v p f) => formula -> formula 
prenex fm =
    foldF q c (\ _ _ -> fm) fm
    where
      q op x p = quant op x (prenex p)
      c (BinOp l (:&:) r) = pullQuants (prenex l .&. prenex r)
      c (BinOp l (:|:) r) = pullQuants (prenex l .|. prenex r)
      c _ = fm

-- |Perform transformations to move quantifiers outside of binary
-- operators:
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
pullQuants :: forall formula term v p f. (FirstOrderLogic formula term v p f) => formula -> formula
pullQuants fm =
    foldF (\ _ _ _ -> fm) pullQuantsCombine (\ _ _ -> fm) fm
    where
      getQuant = foldF (\ op v f -> Just (op, v, f)) (\ _ -> Nothing) (\ _ _ -> Nothing)
      pullQuantsCombine ((:~:) _) = fm
      pullQuantsCombine (BinOp l op r) = 
          case (getQuant l, op, getQuant r) of
            (Just (All, vl, l'),    (:&:), Just (All, vr, r'))    -> pullq True  True  fm for_all (.&.) vl vr l' r'
            (Just (Exists, vl, l'), (:|:), Just (Exists, vr, r')) -> pullq True  True  fm exists  (.|.) vl vr l' r'
            (Just (All, vl, l'),    (:&:), _)                     -> pullq True  False fm for_all (.&.) vl vl l' r
            (_,                     (:&:), Just (All, vr, r'))    -> pullq False True  fm for_all (.&.) vr vr l  r'
            (Just (All, vl, l'),    (:|:), _)                     -> pullq True  False fm for_all (.|.) vl vl l' r
            (_,                     (:|:), Just (All, vr, r'))    -> pullq False True  fm for_all (.|.) vr vr l  r'
            (Just (Exists, vl, l'), (:&:), _)                     -> pullq True  False fm exists  (.&.) vl vl l' r
            (_,                     (:&:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.&.) vr vr l  r'
            (Just (Exists, vl, l'), (:|:), _)                     -> pullq True  False fm exists  (.|.) vl vl l' r
            (_,                     (:|:), Just (Exists, vr, r')) -> pullq False True  fm exists  (.|.) vr vr l  r'
            _                                                     -> fm

-- |Helper function to rename variables when we want to enclose a
-- formula containing a free occurrence of that variable a quantifier
-- that quantifies it.
pullq :: (FirstOrderLogic formula term v p f) =>
         Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> formula
pullq l r fm mkq op x y p q =
    let z = variant (freeVars fm) x
        p' = if l then substitute x (var z) p else p
        q' = if r then substitute y (var z) q else q
        fm' = pullQuants (op p' q') in
    mkq z fm'

-- |Find a variable name which is not in the variables set which is
-- stored in the monad.  This is initialized above with the free
-- variables in the formula.  (FIXME: this is not worth putting in
-- a monad, just pass in the set of free variables.)
variant :: (Enum v, Ord v) => S.Set v -> v -> v
variant names x = if S.member x names then variant names (succ x) else x

-- |We get Skolem Normal Form by skolemizing and then converting to
-- Prenex Normal Form, and finally eliminating the remaining quantifiers.
skolemNormalForm :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolemNormalForm f = askolemize f >>= return . specialize . prenexNormalForm

-- |I need to consult the Harrison book for the reasons why we don't
-- |just Skolemize the result of prenexNormalForm.
askolemize :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
askolemize = skolem . nnf . simplify

-- |Skolemize the formula by removing the existential quantifiers and
-- replacing the variables they quantify with skolem functions (and
-- constants, which are functions of zero variables.)  The Skolem
-- functions are new functions (obtained from the NormalT monad) which
-- are applied to the list of variables which are universally
-- quantified in the context where the existential quantifier
-- appeared.
skolem :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolem fm =
    foldF q c (\ _ _ -> return fm) fm
    where
      q Exists y p =
          do let xs = freeVars fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map var (S.toList xs))
             skolem (substitute y fx p)
      q All x p = skolem p >>= return . for_all x
      c (BinOp l (:&:) r) = skolem2 (.&.) l r
      c (BinOp l (:|:) r) = skolem2 (.|.) l r
      c _ = return fm

skolem2 :: (Monad m, FirstOrderLogic formula term v p f) =>
           (formula -> formula -> formula) -> formula -> formula -> NormalT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

specialize :: FirstOrderLogic formula term v p f => formula -> formula
specialize f =
    foldF q (\ _ -> f) (\ _ _ -> f) f
    where
      q All _ f' = specialize f'
      q _ _ _ = f

-- |Convert to Skolem Normal Form and then distribute the disjunctions over the conjunctions:
-- 
-- @
-- Formula      Rewrites to
-- P | (Q & R)  (P | Q) & (P | R)
-- (Q & R) | P  (Q | P) & (R | P)
-- @
-- 
clauseNormalForm :: (Monad m, FirstOrderLogic formula term v p f, Literal formula) =>
       formula -> NormalT v term m (S.Set (S.Set formula))
clauseNormalForm fm = skolemNormalForm fm >>= return . simpcnf

simpcnf :: forall formula term v p f. (FirstOrderLogic formula term v p f, Literal formula) => formula -> S.Set (S.Set formula)
simpcnf fm =
    foldF (\ _ _ _ -> cjs') (\ _ -> cjs') p fm
    where
      p pr _ts
          | pr == fromBool False = S.empty
          | pr == fromBool True = S.singleton S.empty
          | True = cjs'
      -- Discard any clause that is the proper subset of another clause
      cjs' = S.filter keep cjs
      keep x = not (S.or (S.map (S.isProperSubsetOf x) cjs))
      cjs = S.filter (not . trivial) (purecnf (nnf fm))

-- |Harrison page 59.  Look for complementary pairs in a clause.
trivial :: Literal lit => S.Set lit -> Bool
trivial lits =
    not . S.null $ S.intersection (S.map invert n) p
    where
      (n, p) = S.partition inverted lits

-- | CNF: (a | b | c) & (d | e | f)
purecnf :: forall formula term v p f. FirstOrderLogic formula term v p f => formula -> S.Set (S.Set formula)
purecnf fm =
    foldF (\ _ _ _ -> ss fm) c (\ _ _ -> ss fm) fm
    where
      ss = S.singleton . S.singleton
      -- ((a | b) & (c | d) | ((e | f) & (g | h)) -> ((a | b | e | f) & (c | d | e | f) & (c | d | e | f) & (c | d | g | h))
      c (BinOp l (:|:) r) =
          let lss = purecnf l
              rss = purecnf r in
          S.distrib lss rss
      -- [[a,b],[c,d]] | [[e,f],[g,y]] -> [[a,b],[c,d],[e,f],[g,h]]
      -- a & b -> [[a], [b]]
      c (BinOp l (:&:) r) = S.union (purecnf l) (purecnf r)
      c _ = ss fm

cnfTrace :: (Monad m, FirstOrderLogic formula term v p f, Literal formula, Pretty v, Pretty p, Pretty f) =>
            formula -> NormalT v term m String
cnfTrace f =
    do let simplified = simplify f
           pnf = prenexNormalForm f
       snf <- skolemNormalForm f
       cnf <- clauseNormalForm f
       return . render . vcat $
                  [text "Original:" $$ nest 2 (prettyForm 0 f),
                   text "Simplified:" $$ nest 2 (prettyForm 0 simplified),
                   text "Negation Normal Form:" $$ nest 2 (prettyForm 0 (negationNormalForm f)),
                   text "Prenex Normal Form:" $$ nest 2 (prettyForm 0 pnf),
                   text "Skolem Normal Form:" $$ nest 2 (prettyForm 0 snf),
                   text "Clause Normal Form:" $$ vcat (map prettyClause (fromSS cnf))]
    where
      prettyClause = nest 2 . brackets . hcat . intersperse (text ", ") . map (nest 2 . brackets . prettyForm 0)
      fromSS = (map S.toList) . S.toList 

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
                         (Monad m, FirstOrderLogic formula term v p f, Literal formula, Data formula) =>
                         formula -> NormalT v term m [([formula], [formula])]
implicativeNormalForm formula =
    clauseNormalForm formula >>= return . concatMap split . map (imply . foldl collect ([], [])) . map S.toList . S.toList
    where
      collect :: ([formula], [formula]) -> formula -> ([formula], [formula])
      collect (n, p) f =
          foldF (\ _ _ _ -> error "collect 1")
                (\ cm -> case cm of
                           ((:~:) f') -> (f' : n, p)
                           _ -> error "collect 2")
                (\ _ _ -> (n, f : p))
                f
      imply :: ([formula], [formula]) -> ([formula], [formula])
      imply (n, p) = (reverse n, reverse p)
      split :: ([formula], [formula]) -> [([formula], [formula])]
      split (lhs, rhs) =
          if any isJust (map fromSkolem (gFind rhs :: [f]))
          then map (\ x -> (lhs, [x])) rhs
          else [(lhs, rhs)]

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)
