{-# LANGUAGE OverloadedStrings, RankNTypes, ScopedTypeVariables #-}
module Logic.Harrison
    ( simplify
    , tests
    ) where

import Debug.Trace

import Control.Monad.State (get, put)
import qualified Data.Set as S
import Logic.FirstOrder
import Logic.Logic
import Logic.Monad (NormalT, LogicState(..), runNormal, putVars)

import System.Exit
import Test.HUnit
import Test.Types (V(..), Pr(..), AtomicFunction(..))
import qualified Logic.Instances.Native as N
import Text.PrettyPrint (Doc)

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
      b p (:&:) q = prenex p >>= \ p' -> prenex q >>= \ q' -> pullQuants (p' .&. q')
      b p (:|:) q = prenex p >>= \ p' -> prenex q >>= \ q' -> pullQuants (p' .|. q')
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
      b p (:&:) q = skolem2 (.&.) p q
      b p (:|:) q = skolem2 (.|.) p q
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
                 (runNormal 
                  (pnf (for_all "x" (pApp "p" [var "x"] .|. pApp "r" [var "y"]) .=>.
                        (exists "y" (exists "z" (pApp "q" [var "y"] .|. ((.~.) (exists "z" (pApp "p" [var "z"] .&. pApp "q" [var "z"])))))))))

               , let (x, y, u, v) = (var "x", var "y", var "u", var "v")
                     fv = fApp (toSkolem 2) [u,x]
                     fy = fApp (toSkolem 1) [x] in
                 TestLabel "p150" $ TestCase $
                 assertEqual
                 "snf 150.1"
                 (prettyForm 0 (((.~.) (pApp "<" [x, fy])) .|. pApp "<" [fApp "*" [x, u], fApp "*" [fy, fv]] :: Formula))
                 (prettyForm 0 (runNormal (skolemize (exists "y" (pApp "<" [x, y] .=>. for_all "u" (exists "v" (pApp "<" [fApp "*" [x, u],
                                                                                                 fApp "*" [y, v]])))))))

               , let p x = pApp "p" [x]
                     q x = pApp "q" [x]
                     (x, y, z) = (var "x", var "y", var "z") in
                 TestLabel "p150" $ TestCase $
                 assertEqual
                 "snf 150.2"
                 (((.~.) (p x)) .|. (q (fApp (toSkolem 1) []) .|. (((.~.) (p z)) .|. ((.~.) (q z)))) :: Formula)
                 (runNormal (skolemize (for_all "x" (p x .=>. (exists "y" (exists "z" (q y .|. (.~.) (exists "z" (p z .&. (q z))))))))))
               ]) >>=
    \ counts -> exitWith (if errors counts /= 0 || failures counts /= 0 then ExitFailure 1 else ExitSuccess)

instance Eq Doc where
    a == b = show a == show b
