{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Logic.Harrison
    ( simplify
    , tests
    ) where

import Debug.Trace

import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic

import System.Exit
import Test.HUnit
import Test.Types (V(..), Pr(..), AtomicFunction(..))
import qualified Logic.Instances.Native as N

true = pApp (fromBool True) []

false = pApp (fromBool False) []

-- |p. 51
-- negative = foldF (const True) (\ _ _ _ -> False) (\ _ _ _ -> False) (\ _ _ _ -> False) (\ _ _ -> False)

psimplify :: FirstOrderLogic formula term v p f => formula -> formula
psimplify fm =
    foldF (\ p -> psimplify1 ((.~.) (psimplify p)))
          (\ op v fm' -> error "psimplify")
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
          | True = pApp pr ts
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
                    (\ pr ts -> if pr == fromBool True
                                then Just True
                                else if pr == fromBool False
                                     then Just False
                                     else Nothing)
      true = pApp (fromBool True) []
      false = pApp (fromBool False) []

-- |Bottom recursion to simplify a formula.
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
          (\ op v p -> if S.member v (freeVars p) then fm else p)
          (\ _ _ _ -> psimplify1 fm)
          (\ _ _ _ -> psimplify1 fm)
          (\ _ _ -> psimplify1 fm)
          fm

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

pullQuants fm =
    foldF (\ _ -> fm) (\ _ _ _ -> fm) pullQuantsBinop (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      getQuant = foldF (\ _ -> Nothing) (\ op v f -> Just (op, v, f)) (\ _ _ _ -> Nothing) (\ _ _ _ -> Nothing) (\ _ _ -> Nothing)
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
            _                                                     -> fm

pullq :: FirstOrderLogic formula term v p f => Bool -> Bool -> formula -> (v -> formula -> formula) -> (formula -> formula -> formula) -> v -> v -> formula -> formula -> formula
pullq l r fm mkq op x y p q =
    let z = variant x (freeVars fm)
        p' = if l then substitute x (var z) p else p
        q' = if r then substitute y (var z) q else q in
    mkq z (pullQuants (op p' q'))

variant x s = if S.member x s then variant (succ x) s else x

prenex fm =
    foldF (\ _ -> fm) q b (\ _ _ _ -> fm) (\ _ _ -> fm) fm
    where
      q op x p = quant op x (prenex p)
      b p (:&:) q = pullQuants (prenex p .&. prenex q)
      b p (:|:) q = pullQuants (prenex p .|. prenex q)
      b _ _ _ = fm

pnf = prenex . nnf . simplify

{-
skolem fm =
    foldF n q b i p fm
    where
      n _ = return fm
      q Exists (y:ys) p =
          do state <- get
          let state' = state {skolemCount = skolemCount state + 1}
          let xs = freeVars fm in
          let f = toSkolem (skolemCount state)
          let fx = fApp f (map var xs)
          skolem (subst (y |=> fx) p)

skolem2 cons (p, q) fns =
    let (p', fns') = skolem q fns in
    let (q', fns'') = skolem q fns' in
    ((p', q'), fns)

askolemize fm =
    skolem (nnf (simplify f))

specialize :: FirstOrderLogic formula term v p f => formula -> formula
specialize f =
    foldF (\ _ -> f) q (\ _ _ _ -> f) (\ _ _ -> f) f
    where
      q _ All f' = specialize f'
      q _ _ _ = f

skolemize = specialize . pnf . askolemize
-}

type Formula = N.Formula V Pr AtomicFunction

tests :: IO ()
tests =
    let p = pApp "p" []
        q = pApp "q" [] in
    runTestTT (TestList 
               [ TestLabel "p50" $ TestCase $
                 assertEqual
                 "psimplify 50"
                 (p .<=>. (.~.) p :: Formula)
                 (simplify $ true .=>. (p .<=>. (p .<=>. false)))
               , TestLabel "p51" $ TestCase $
                 assertEqual
                 "psimplify 51"
                 (true :: Formula)
                 (simplify (((pApp "x" [] .=>. pApp "y" []) .=>. true) .|. false))
               , TestLabel "p140" $ TestCase $
                 assertEqual
                 "simplify 140.3"
                 ((for_all "x" (pApp "p" [var "x"])) .=>. (pApp "q" []))
                 (simplify ((for_all "x" (for_all "y" (pApp "p" [var "x"] .|. (pApp "p" [var "y"] .&. false))) .=>. (exists "z" q))))
               , TestLabel "p141" $ TestCase $
                 assertEqual
                 "nnf 141.1"
                 ((exists "x" ((.~.) (pApp (Pr "p") [var "x"]))) .|.
                  ((((exists "y" (pApp (Pr "q") [var "y"])) .&. ((exists "z" ((pApp (Pr "p") [var "z"]) .&. ((pApp (Pr "q") [var "z"])))))) .|.
                    (((for_all "y" ((.~.) (pApp (Pr "q") [var "y"]))) .&. ((for_all "z" (((.~.) (pApp (Pr "p") [var "z"])) .|. (((.~.) (pApp (Pr "q") [var "z"])))))))))) :: Formula)
                 (nnf ((for_all "x" (pApp "p" [var "x"])) .=>. ((exists "y" (pApp "q" [var "y"])) .<=>. (exists "z" (pApp "p" [var "z"] .&. pApp "q" [var "z"])))))
               , TestLabel "p144" $ TestCase $
                 assertEqual
                 "pnf 144.1"
                 (exists "x" 
                  (for_all "z"
                   ((((.~.) (pApp "p" [var "x"])) .&. (((.~.) (pApp "r" [var "y"])))) .|.
                    (((pApp "q" [var "x"]) .|. ((((.~.) (pApp "p" [var "z"])) .|. (((.~.) (pApp "q" [var "z"]))))))))) :: Formula)
                 (pnf (for_all "x" (pApp "p" [var "x"] .|. pApp "r" [var "y"]) .=>.
                       (exists "y" (exists "z" (pApp "q" [var "y"] .|. ((.~.) (exists "z" (pApp "p" [var "z"] .&. pApp "q" [var "z"]))))))))
               ]) >>=
    \ counts -> exitWith (if errors counts /= 0 || failures counts /= 0 then ExitFailure 1 else ExitSuccess)
