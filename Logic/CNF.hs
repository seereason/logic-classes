{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Logic.CNF
    ( cnf
    , cnf'
    , simplify
    , moveNegationsIn
    , skolemize
    , moveQuantifiersOut
    , distributeDisjuncts
    ) where

import Debug.Trace
import qualified Data.Set as S
import Logic.Logic
import Logic.Predicate

cnf :: (PredicateLogic formula term v p f, Skolem v f, Eq formula, Eq term, Enum v) => formula -> formula
cnf = distributeDisjuncts . skolemize [] . moveQuantifiersOut . moveNegationsIn . simplify

cnf' :: (PredicateLogic formula term v p f, Skolem v f, Eq formula, Eq term, Enum v, Show v, Show p, Show f) => formula -> formula
cnf' = t6 . distributeDisjuncts . t5 . skolemize [] . t4 . moveQuantifiersOut . t3 . moveNegationsIn . t2 . simplify . t1
    where
      t1 x = trace ("input:               " ++ showForm x) x
      t2 x = trace ("simplified:          " ++ showForm x) x
      t3 x = trace ("moveNegationsIn:     " ++ showForm x) x
      t4 x = trace ("moveQuantifiersOut:  " ++ showForm x) x
      t5 x = trace ("skolmize:            " ++ showForm x) x
      t6 x = trace ("distributeDisjuncts: " ++ showForm x) x

skolemize :: (PredicateLogic formula term v p f, Skolem v f, Eq formula, Eq term) => [v] -> formula -> formula
skolemize uq =
    foldF n q b i a
    where
      n x = (.~.) (skolemize uq x)
      -- ∃x: p x is satisfiable <=> p x is satisfiable, so we can discard outermost.
      q Exists _ x | uq == [] = skolemize uq x
      q Exists vs x = skolemize uq (substituteTerms pairs x) where pairs = zip (map (skolemFunction uq) vs) (map var vs)
      q All vs x = skolemize (vs ++ uq) x
      b = binOp
      i = infixPred
      a = pApp

skolemFunction :: (PredicateLogic formula term v p f, Skolem v f) => [v] -> v -> term
skolemFunction uq v = fApp (skolem v) (map var uq)

{-
1st order formula
∀Y (∀X (taller(Y,X) | wise(X)) => wise(Y))

Simplify
∀Y (~∀X (taller(Y,X) | wise(X)) | wise(Y))

Move negations in
∀Y (∃X (~taller(Y,X) & ~wise(X)) | wise(Y))

Move quantifiers out
∀Y (∃X ((~taller(Y,X) & ~wise(X)) | wise(Y)))

Skolemize
∃X ((~taller(Y,X) & ~wise(X)) | wise(Y)) γ = {Y}
(~taller(Y,x(Y)) & ~wise(x(Y))) | wise(Y)

Distribute disjunctions
(~taller(Y,x(Y)) | wise(Y)) & (~wise(x(Y)) | wise(Y))

Convert to CNF
{ ~taller(Y,x(Y)) | wise(Y),
~wise(x(Y)) | wise(Y) } 
-}

{-
Simplify:

P <~> Q 	(P | Q) & (~P | ~Q)
P <=> Q 	(P => Q) & (Q => P)
P => Q  	~P | Q
-}

simplify :: PredicateLogic formula term v p f => formula -> formula
simplify =
    foldF n q b i a
    where
      q All vs f = for_all vs (simplify f)
      q Exists vs f = exists vs (simplify f)
      b :: PredicateLogic formula term v p f => formula -> BinOp -> formula -> formula
      b f1 (:&:) f2 = simplify f1 .&. simplify f2
      b f1 (:|:) f2 = simplify f1 .|. simplify f2
      b f1 (:=>:) f2 = ((.~.) (simplify f1)) .|. simplify f2
      -- b f1 (:<=>:) f2 = simplify (f1 .=>. f2 .&. f2 .=>. f1)
      b f1 (:<=>:) f2 = simplify ((((.~.) (simplify f1)) .|. simplify f2) .&. (((.~.) (simplify f2)) .|. simplify f1))
      n f = (.~.) (simplify f)
      i t1 (:=:) t2 = t1 .=. t2
      i t1 (:!=:) t2 = t1 .!=. t2
      a p ts = pApp p ts
{-
removeArrows (Forall x y) = Forall x (removeArrows y)
removeArrows (Exists x y) = Exists x (removeArrows y)
removeArrows (Not a)    = makeNeg  (removeArrows a)
removeArrows (a :& b)   = makeConj (removeArrows a) (removeArrows b)
removeArrows (a :\/ b)  = makeDisj (removeArrows a) (removeArrows b)
removeArrows (a :-> b)  = makeDisj (makeNeg (removeArrows a)) (removeArrows b)
removeArrows (a :<-> b) = makeDisj (makeConj(removeArrows a)  (removeArrows b))
                                   (makeConj(makeNeg (removeArrows a)) 
                                            (makeNeg(removeArrows b)))
removeArrows  e = e
-}

{-
Move negations in
Formula	Rewrites to
~∀X P 	∃X ~P
~∃X P 	∀X ~P
~(P & Q) 	(~P | ~Q)
~(P | Q) 	(~P & ~Q)
~~P 	P
-}

moveNegationsIn :: PredicateLogic formula term v p f => formula -> formula
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
      doNegation :: PredicateLogic formula term v p f => formula -> formula
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


-- |Move quantifiers out
-- 
-- > Formula	Rewrites to
-- > ∀X P & Q 	∀X (P & Q)
-- > ∃X P & Q 	∃X (P & Q)
-- > Q & ∀X P 	∀X (Q & P)
-- > Q & ∃X P 	∃X (Q & P)
-- > ∀X P | Q 	∀X (P | Q)
-- > ∃X P | Q 	∃X (P | Q)
-- > Q | ∀X P 	∀X (Q | P)
-- > Q | ∃XP 	∃X (Q | P)
-- 
-- We also need to do some variable renaming here, so that in an
-- example like @∀X P & Q -> ∀X (P & Q)@ there are no references to X
-- in Q.  We choose to examine Q and if X appears there, find another
-- variable which does not appear and change occurrences of X in P to
-- this new variable.  We could instead modify Q, but that looks
-- slightly more tedious.
moveQuantifiersOut :: forall formula term v p f. (PredicateLogic formula term v p f, Enum v) => formula -> formula
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

-- Find new variables that are not in the set and substitute free
-- occurrences in the formula.
renameFreeVars :: PredicateLogic formula term v p f => S.Set v -> [v] -> formula -> ([v], formula)
renameFreeVars s vs f =
    (vs'', foldr (\ (new, old) f' -> substitute' new old f') f (zip vs'' vs))
    where
      (vs'', _) = foldr (\ v (vs', s') -> let v' = findName s' v in (v' : vs', S.insert v' s')) ([], s) vs
      findName s' v = if S.member v s' then findName s' (succ v) else v

{-
distdisjuncts (a :\/ (b :& c)) 
 | a == b    = distdisjuncts a
 | a == c    = distdisjuncts a 
 | otherwise = distdisjuncts  (makeConj (distdisjuncts (makeDisj a b))  
                                        (distdisjuncts (makeDisj a c)))

distdisjuncts ((a :& b) :\/ c) 
 | c == b    = distdisjuncts c
 | c == a    = distdisjuncts c
 | otherwise = distdisjuncts (makeConj (distdisjuncts(makeDisj c a))
                                       (distdisjuncts(makeDisj c b)))

distdisjuncts (a :&  b)  =  makeConj (distdisjuncts a) (distdisjuncts b)
distdisjuncts (a :\/ b)  =  makeDisj (distdisjuncts a) (distdisjuncts b)
distdisjuncts e = e
-}

{-
Distribute disjunctions
Formula	Rewrites to
P | (Q & R) 	(P | Q) & (P | R)
(Q & R) | P 	(Q | P) & (R | P)
-}            

-- a|(b&c) -> (a|b)&(a|c)
distributeDisjuncts :: (Eq formula, PredicateLogic formula term v p f) => formula -> formula
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
            b' f3 (:&:) f4
                | f1 == f3 || f1 == f4 = distributeDisjuncts f1
                | otherwise = distributeDisjuncts (distributeDisjuncts (f1 .|. f3) .&. distributeDisjuncts (f1 .|. f4))
            b' _ _ _ = doLHS f1 f2
            q' _ _ _ = doLHS f1 f2
            i' _ _ _ = doLHS f1 f2
            a' _ _ = doLHS f1 f2
      doLHS f1 f2 =
          foldF n' q' b' i' a' f1
          where
            n' _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            q' _ _ _ =  distributeDisjuncts f1 .|. distributeDisjuncts f2
            b' f3 (:&:) f4
                -- Quick simplification: p & (p | q) == p
                | f2 == f3 ||  f2 == f4 = distributeDisjuncts f2
                | otherwise = distributeDisjuncts (distributeDisjuncts (f3 .|. f2) .&. distributeDisjuncts (f4 .|. f2))
            b' _ _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            i' _ _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            a' _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
