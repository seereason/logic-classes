{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Logic.Harrison
    ( psimplify
    , simplify
    , negationNormalForm
    , pnf
    , skolemize
    , dnf
    , cnf
    , trivial
    ) where

import Control.Monad.State (get, put)
import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Clause (Literal(..))
import Logic.Logic
import Logic.Monad (NormalT, LogicState(..), putVars)
import qualified Logic.Set as S
import Prelude hiding (negate)

-- |p. 51
-- negative = foldF (const True) (\ _ _ _ -> False) (\ _ _ _ -> False) (\ _ _ _ -> False) (\ _ _ -> False)

psimplify :: FirstOrderLogic formula term v p f => formula -> formula
psimplify fm =
    foldF (\ p -> psimplify1 ((.~.) (psimplify p)))
          (\ _op _v _fm' -> error "psimplify")
          (\ l op r -> psimplify1 (binOp (psimplify l) op (psimplify r)))
          (\ l op r -> psimplify1 (infixPred l op r))
          (\ pr ts -> psimplify1 (pApp pr ts))
          fm

-- Ugh, implementing this polymorphically is really painful for some
-- reason.
psimplify1 :: forall formula term v p f. FirstOrderLogic formula term v p f => formula -> formula
psimplify1 fm =
    foldF simplifyNot (\ _ _ _ -> fm) simplifyBinOp (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      simplifyNot = foldF id (\ _ _ _ -> fm) (\ _ _ _ -> fm) (\ _ _ _ -> fm) simplifyNotPred
      simplifyNotPred pr ts
          | pr == fromBool False = pApp (fromBool True) ts
          | pr == fromBool True = pApp (fromBool False) ts
          | True = (.~.) (pApp pr ts)
      simplifyBinOp l op r =
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
      -- Return a Maybe Bool depending upon whether a formula is true,
      -- false, or something else.
      pBool :: formula -> Maybe Bool
      pBool = foldF (\ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing)
                    (\ pr _ts -> if pr == fromBool True
                                 then Just True
                                 else if pr == fromBool False
                                      then Just False
                                      else Nothing)
      true = pApp (fromBool True) []
      false = pApp (fromBool False) []

-- |Bottom-up recursion to simplify a formula.
simplify :: FirstOrderLogic formula term v p f => formula -> formula
simplify fm =
    foldF (\ p -> simplify1 ((.~.) (simplify p)))
          (\ op v p -> simplify1 (quant op v (simplify p)))
          (\ p op q -> simplify1 (binOp (simplify p) op (simplify q)))
          (\ _ _ _ -> simplify1 fm)
          (\ _ _ -> simplify1 fm)
          fm

-- |Extend psimplify1 to handle quantifiers.
simplify1 :: FirstOrderLogic formula term v p f => formula -> formula
simplify1 fm =
    foldF (\ _ -> psimplify1 fm)
          (\ _op v p -> if S.member v (freeVars p) then fm else p)
          (\ _ _ _ -> psimplify1 fm)
          (\ _ _ _ -> psimplify1 fm)
          (\ _ _ -> psimplify1 fm)
          fm

nnf :: FirstOrderLogic formula term v p f => formula -> formula
nnf fm =
    foldF nnfNot nnfQuant nnfBinOp (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      nnfNot p = foldF nnf nnfNotQuant nnfNotBinOp (\ _ _ _ -> fm) (\ _ _ -> fm) p
      nnfQuant op v p = quant op v (nnf p)
      nnfBinOp p (:=>:) q = nnf ((.~.) p) .|. (nnf q)
      nnfBinOp p (:<=>:) q =  (nnf p .&. nnf q) .|. (nnf ((.~.) p) .&. nnf ((.~.) q))
      nnfBinOp p (:&:) q = nnf p .&. nnf q
      nnfBinOp p (:|:) q = nnf p .|. nnf q
      nnfNotQuant All v p = exists v (nnf ((.~.) p))
      nnfNotQuant Exists v p = for_all v (nnf ((.~.) p))
      nnfNotBinOp p (:&:) q = nnf ((.~.) p) .|. nnf ((.~.) q)
      nnfNotBinOp p (:|:) q = nnf ((.~.) p) .&. nnf ((.~.) q)
      nnfNotBinOp p (:=>:) q = nnf p .&. nnf ((.~.) q)
      nnfNotBinOp p (:<=>:) q = (nnf p .&. nnf ((.~.) q)) .|. nnf ((.~.) p) .&. nnf q

negationNormalForm :: FirstOrderLogic formula term v p f => formula -> formula
negationNormalForm = nnf . simplify

pullQuants :: forall m formula term v p f. (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
pullQuants fm =
    foldF (\ _ -> return fm) (\ _ _ _ -> return fm) pullQuantsBinop (\ _ _ _ -> return fm) (\ _ _ -> return fm) fm
    where
      getQuant = foldF (\ _ -> Nothing) (\ op v f -> Just (op, v, f)) (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ _ -> Nothing)
      pullQuantsBinop :: formula -> BinOp -> formula -> NormalT v term m formula
      pullQuantsBinop l op r = 
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
            _                                                     -> return fm

pullq :: (Monad m, FirstOrderLogic formula term v p f) =>
         Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> NormalT v term m formula
pullq l r fm mkq op x y p q =
    do z <- putVars (freeVars fm) >> variant x
       let p' = if l then substitute x (var z) p else p
           q' = if r then substitute y (var z) q else q
       fm' <- pullQuants (op p' q')
       return $ mkq z fm'

variant :: (Monad m, FirstOrderLogic formula term v p f) => v -> NormalT v term m v
variant x =
    do state <- get
       let names = varNames state
       if S.member x names then variant (succ x) else
           do put (state {varNames = S.insert x names})
              return x

prenex :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula 
prenex fm =
    foldF (\ _ -> return fm) q b (\ _ _ _ -> return fm) (\ _ _ -> return fm) fm
    where
      q op x p = prenex p >>= return . quant op x
      b l (:&:) r = prenex l >>= \ l' -> prenex r >>= \ r' -> pullQuants (l' .&. r')
      b l (:|:) r = prenex l >>= \ l' -> prenex r >>= \ r' -> pullQuants (l' .|. r')
      b _ _ _ = return fm

pnf :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
pnf = prenex . nnf . simplify

skolem :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolem fm =
    foldF (\ _ -> return fm) q b (\ _ _ _ -> return fm) (\ _ _ -> return fm) fm
    where
      q Exists y p =
          do let xs = freeVars fm
             state <- get
             let f = toSkolem (skolemCount state)
             put (state {skolemCount = skolemCount state + 1})
             let fx = fApp f (map var (S.toList xs))
             skolem (substitute y fx p)
      q All x p = skolem p >>= return . for_all x
      b l (:&:) r = skolem2 (.&.) l r
      b l (:|:) r = skolem2 (.|.) l r
      b _ _ _ = return fm

skolem2 :: (Monad m, FirstOrderLogic formula term v p f) => (formula -> formula -> formula) -> formula -> formula -> NormalT v term m formula
skolem2 cons p q =
    skolem p >>= \ p' ->
    skolem q >>= \ q' ->
    return (cons p' q')

askolemize :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
askolemize = skolem . nnf . simplify

specialize :: FirstOrderLogic formula term v p f => formula -> formula
specialize f =
    foldF (\ _ -> f) q (\ _ _ _ -> f) (\ _ _ _ -> f) (\ _ _ -> f) f
    where
      q All _ f' = specialize f'
      q _ _ _ = f

skolemize :: (Monad m, FirstOrderLogic formula term v p f) => formula -> NormalT v term m formula
skolemize f = askolemize f >>= pnf >>= return . specialize

-- | @a&(b|c) -> (a|b)&(a|c)@
distribDNF :: FirstOrderLogic formula term v p f => formula -> formula
distribDNF f =
    foldF (\ _ -> f) (\ _ _ _ -> f) b (\ _ _ _ -> f) (\ _ _ -> f) f
    where
      b l (:&:) r =
          case (ors l, ors r) of
            (_, Just (l', r')) -> distribDNF (l .&. l') .|. distribDNF (l .&. r')
            (Just (l', r'), _) -> distribDNF (l' .&. r) .|. distribDNF (r' .&. r)
            _ -> f
      b _ _ _ = f
      ors = foldF (\ _ -> Nothing)
                  (\ _ _ _ -> Nothing) 
                  (\ l' op r' -> if op == (:|:) then Just (l', r') else Nothing)
                  (\ _ _ _ -> Nothing)
                  (\ _ _ -> Nothing)

rawdnf :: FirstOrderLogic formula term v p f => formula -> formula
rawdnf fm =
    foldF (\ _ -> fm) (\ _ _ _ -> fm) b (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      b l (:&:) r = distribDNF (rawdnf l .&. rawdnf r)
      b l (:|:) r = distribDNF (rawdnf l .|. rawdnf r)
      b _ _ _ = fm

-- | @a|(b&c) -> (a&b)|(a&c)@
distribCNF :: FirstOrderLogic formula term v p f => Logic formula => formula -> formula
distribCNF f =
    foldF (\ _ -> f) (\ _ _ _ -> f) b (\ _ _ _ -> f) (\ _ _ -> f) f
    where
      b l (:|:) r =
          case (ands l, ands r) of
            (_, Just (l', r')) -> distribCNF (l .|. l') .&. distribCNF (l .|. r')
            (Just (l', r'), _) -> distribCNF (l' .|. r) .&. distribCNF (r' .|. r)
            _ -> f
      b _ _ _ = f
      ands = foldF (\ _ -> Nothing)
                   (\ _ _ _ -> Nothing)
                   (\ l' op r' -> if op == (:&:) then Just (l', r') else Nothing)
                   (\ _ _ _ -> Nothing)
                   (\ _ _ -> Nothing)

rawcnf :: FirstOrderLogic formula term v p f => formula -> formula
rawcnf fm =
    foldF (\ _ -> fm) (\ _ _ _ -> fm) b (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      b l (:&:) r = distribCNF (rawcnf l .&. rawcnf r)
      b l (:|:) r = distribCNF (rawcnf l .|. rawcnf r)
      b _ _ _ = fm

-- | DNF: (a & b & c) | (d & e & f)
purednf :: forall formula term v p f. FirstOrderLogic formula term v p f => formula -> S.Set (S.Set formula)
purednf fm =
    foldF (\ _ -> ss fm) (\ _ _ _ -> ss fm) b (\ _ _ _ -> ss fm) (\ _ _ -> ss fm) fm
    where
      ss = S.singleton . S.singleton
      b :: formula -> BinOp -> formula -> S.Set (S.Set formula)
      b l (:&:) r =
          let lss = purednf l
              rss = purednf r in
          S.flatten $ S.map (\ (rs :: S.Set formula) -> (S.map (\ (ls :: S.Set formula) -> S.union rs ls) lss)) rss
      b l (:|:) r = S.union (purednf l) (purednf r)
      b _ _ _ = ss fm

simpdnf :: forall formula term v p f. (FirstOrderLogic formula term v p f, Literal formula) => formula -> S.Set (S.Set formula)
simpdnf fm =
    foldF (\ _ -> djs') (\ _ _ _ -> djs') (\ _ _ _ -> djs') (\ _ _ _ -> djs') p fm
    where
      p pr ts =
          if pr == fromBool False
          then S.empty
          else if pr == fromBool True
               then S.singleton S.empty
               else djs'
      djs' :: S.Set (S.Set formula)
      djs' = S.filter (\ d -> not (S.any (`S.isProperSubsetOf` d) djs)) djs
      djs :: S.Set (S.Set formula)
      djs = S.filter (not . trivial) (purednf (nnf fm))

-- (a&b) | (c&d)
dnf :: (Monad m, FirstOrderLogic formula term v p f, Literal formula) =>
       formula -> NormalT v term m (S.Set (S.Set formula))
dnf fm = skolemize fm >>= return . S.filter (not . trivial) . purednf

-- | CNF: (a | b | c) & (d | e | f)
purecnf :: forall formula term v p f. FirstOrderLogic formula term v p f => formula -> S.Set (S.Set formula)
purecnf fm =
    foldF (\ _ -> ss fm) (\ _ _ _ -> ss fm) b (\ _ _ _ -> ss fm) (\ _ _ -> ss fm) fm
    where
      ss = S.singleton . S.singleton
      b :: formula -> BinOp -> formula -> S.Set (S.Set formula)
      -- ((a | b) & (c | d) | ((e | f) & (g | h)) -> ((a | b | e | f) & (c | d | e | f) & (c | d | e | f) & (c | d | g | h))
      b l (:|:) r =
          let lss = purecnf l
              rss = purecnf r in
          S.distrib lss rss
      -- [[a,b],[c,d]] | [[e,f],[g,y]] -> [[a,b],[c,d],[e,f],[g,h]]
      -- a & b -> [[a], [b]]
      b l (:&:) r = S.union (purecnf l) (purecnf r)
      b _ _ _ = ss fm

simpcnf :: forall formula term v p f. (FirstOrderLogic formula term v p f, Literal formula) => formula -> S.Set (S.Set formula)
simpcnf fm =
    foldF (\ _ -> cjs') (\ _ _ _ -> cjs') (\ _ _ _ -> cjs') (\ _ _ _ -> cjs') p fm
    where
      p pr ts
          | pr == fromBool False = S.empty
          | pr == fromBool True = S.singleton S.empty
          | True = cjs'
      -- Discard any clause that is the proper subset of another clause
      cjs' = S.filter keep cjs
      keep x = not (S.or (S.map (S.isProperSubsetOf x) cjs))
      -- cjs' = cjs
      -- cjs' = S.filter (\ d -> not (S.any (`S.isProperSubsetOf` d) cjs)) cjs
      cjs = S.filter (not . trivial) (purecnf (nnf fm))

-- (a|b) & (c|d)
cnf :: (Monad m, FirstOrderLogic formula term v p f, Literal formula) =>
       formula -> NormalT v term m (S.Set (S.Set formula))
cnf fm = skolemize fm >>= return . simpcnf -- S.filter (not . trivial) . purecnf

-- |Harrison page 59.  Look for complementary pairs in a clause.
trivial :: Literal lit => S.Set lit -> Bool
trivial lits =
    not . S.null $ S.intersection (S.map invert n) p
    where
      (n, p) = S.partition inverted lits
