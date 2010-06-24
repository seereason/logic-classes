module Logic.CNF
    ( cnf
    , cnf'
    , simplify
    , moveNegationsIn
    , skolemize
    , moveQuantifiersOut
    ) where

import Debug.Trace
import Data.String
import Logic.Predicate

cnf :: (Eq formula, Eq term, PredicateLogic formula atom term v p f, Show formula) => formula -> formula
cnf = distributeDisjuncts . skolemize [] . moveQuantifiersOut . moveNegationsIn . simplify

cnf' :: (Eq formula, Eq term, PredicateLogic formula atom term v p f, Show formula) => formula -> formula
cnf' = t6 . distributeDisjuncts . t5 . skolemize [] . t4 . moveQuantifiersOut . t3 . moveNegationsIn . t2 . simplify . t1
    where
      t1 x = trace ("input:               " ++ show x) x
      t2 x = trace ("simplified:          " ++ show x) x
      t3 x = trace ("moveNegationsIn:     " ++ show x) x
      t4 x = trace ("moveQuantifiersOut:  " ++ show x) x
      t5 x = trace ("skolmize:            " ++ show x) x
      t6 x = trace ("distributeDisjuncts: " ++ show x) x

skolemize :: (Eq formula, Eq term, PredicateLogic formula atom term v p f) => [v] -> formula -> formula
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

skolemFunction :: (IsString f, PredicateLogic formula atom term v p f) => [v] -> v -> term
skolemFunction uq v = fApp (fromString (toString v)) (map var uq)

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

simplify :: PredicateLogic formula atom term v p f => formula -> formula
simplify =
    foldF n q b i a
    where
      q All vs f = for_all vs (simplify f)
      q Exists vs f = exists vs (simplify f)
      b :: PredicateLogic formula atom term v p f => formula -> BinOp -> formula -> formula
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

moveNegationsIn :: PredicateLogic formula atom term v p f => formula -> formula
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
      doNegation :: PredicateLogic formula atom term v p f => formula -> formula
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

{-
Move quantifiers out
Formula	Rewrites to
∀X P & Q 	∀X (P & Q)
∃X P & Q 	∃X (P & Q)
Q & ∀X P 	∀X (Q & P)
Q & ∃X P 	∃X (Q & P)
∀X P | Q 	∀X (P | Q)
∃X P | Q 	∃X (P | Q)
Q | ∀X P 	∀X (Q | P)
Q | ∃XP 	∃X (Q | P)
-}

moveQuantifiersOut :: (PredicateLogic formula atom term v p f, Show formula) => formula -> formula
moveQuantifiersOut formula =
    {- tr $ -} foldF n q b i a formula
    where
      -- We don't need to do this because we've already moved the
      -- negations inside all the quantifiers
      n = (.~.)
      q All vs f = for_all vs (moveQuantifiersOut f)
      q Exists vs f = exists vs (moveQuantifiersOut f)
      b f1 op f2 = doLHS (moveQuantifiersOut f1) op (moveQuantifiersOut f2)
      i t1 op t2 = infixPred t1 op t2
      a p ts = pApp p ts
      -- We found :&: or :|: above, look for quantifiers to move out, first examine f1
      doLHS :: (PredicateLogic formula atom term v p f, Show formula) => formula -> BinOp -> formula -> formula
      doLHS f1 op f2 =
          foldF n' q' b' i' a' f1
          where
            n' _ = doRHS f1 op f2
            q' All vs f = for_all vs (moveQuantifiersOut (doBinOp f op f2))
            q' Exists vs f = exists vs (moveQuantifiersOut (doBinOp f op f2))
            b' _ _ _ = doRHS f1 op f2
            i' _ _ _ = doRHS f1 op f2
            a' _ _ = doRHS f1 op f2
      -- We reached a point where f1 was not a quantifier, try f2
      doRHS :: (PredicateLogic formula atom term v p f, Show formula) => formula -> BinOp -> formula -> formula
      doRHS f1 op f2 =
          foldF n' q' b' i' a' f2
          where
            n' _ = doBinOp f1 op f2
            q' All vs f = for_all vs (moveQuantifiersOut (doBinOp f1 op f))
            q' Exists vs f = exists vs (moveQuantifiersOut (doBinOp f1 op f))
            b' _ _ _ = doBinOp f1 op f2
            i' _ _ _ = doBinOp f1 op f2
            a' _ _ = doBinOp f1 op f2
      doBinOp :: (PredicateLogic formula atom term v p f, Show formula) => formula -> BinOp -> formula -> formula
      doBinOp f1 (:&:) f2 = f1 .&. f2
      doBinOp f1 (:|:) f2 = f1 .|. f2
      doBinOp _ op _ = error $ "moveQuantifierOut: unexpected BinOp " ++ show op
      -- tr x = trace ("moveQuantifiersOut:\n formula=" ++ show formula ++ "\n  result=" ++ show x) x
          
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
distributeDisjuncts :: (Eq formula, PredicateLogic formula atom term v p f) => formula -> formula
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
