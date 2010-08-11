{-# LANGUAGE RankNTypes #-}
module Logic.Resolution
    ( prove
    , getSetOfSupport
    , SetOfSupport
    , Unification
    , Subst
    ) where

import qualified Data.Set as S
import Logic.FirstOrder (FirstOrderLogic(..))
import Logic.Implicative (Implicative(..))
import Logic.NormalForm ()

type SetOfSupport inf v term = [Unification inf v term]
type Unification inf v term = (inf, Subst v term)
type Subst v term = [(v, term)]

prove :: (Implicative inf formula term v p f) => SetOfSupport inf v term -> SetOfSupport inf v term -> [inf] -> (Bool, SetOfSupport inf v term)
prove ss1 [] _kb = (False, ss1)
prove ss1 (s:ss2) kb =
    case tf of
      True -> (True, (ss1 ++ [s] ++ ss'))
      False -> prove (ss1 ++ [s]) ss' (fst s : kb)
    where
      (ss', tf) = prove' s kb ss2 ss1

prove' :: (Implicative inf formula term v p f) => Unification inf v term -> [inf] -> SetOfSupport inf v term -> SetOfSupport inf v term -> (SetOfSupport inf v term, Bool)
prove' p kb ss1 ss2 =
    case result of
      ([], _) -> (ss1, False)
      (l, tf) -> (ss1 ++ l, tf)
    where
      res1 = map (\x -> resolution p (x,[])) kb
      res2 = map (\x -> resolution (x,[]) p) kb
      dem1 = map (\e -> demodulate p (e,[])) kb
      dem2 = map (\p' -> demodulate (p',[]) p) kb
      result = getResult (ss1 ++ ss2) (res1 ++ res2 ++ dem1 ++ dem2)

getResult :: (Implicative inf formula term v p f) => SetOfSupport inf v term -> [Maybe (Unification inf v term)] -> (SetOfSupport inf v term, Bool)
getResult _ [] = ([], False)
getResult ss (Nothing:xs) = getResult ss xs
getResult ss ((Just x@(inf, subst)):xs)  =
    if null (neg inf) && null (pos inf)
    then ([x], True)
    else if or (map (\(e,_) -> isRenameOf (fst x) e) ss)
         then getResult ss xs
         else let (xs', tf) = getResult ss xs in (x:xs', tf)


-- resolution :: (Eq v, Eq p, Eq f) => Unification v p f -> Unification v p f -> Maybe (Unification v p f)
resolution (inf1 {-(INF lhs1 rhs1)-}, theta1) (inf2 {-(INF lhs2 rhs2)-}, theta2) =
    let
      unifyResult = tryUnify (pos inf1) (neg inf2)
    in
      case unifyResult of
        Just ((rhs1', theta1'), (lhs2', theta2')) ->
            let
              lhs'' = map (\s -> subst s theta1') (neg inf1) ++
                      map (\s -> subst s theta2') lhs2'
              rhs'' = map (\s -> subst s theta1') rhs1' ++
                      map (\s -> subst s theta2') (pos inf2)
              theta = updateSubst theta1 theta1' ++
		      updateSubst theta2 theta2'
            in
              Just (makeINF lhs'' rhs'', theta)
        Nothing -> Nothing

tryUnify :: Implicative inf clause => [clause] -> [clause] -> Maybe (([clause], Subst v term), ([clause], Subst v term))
tryUnify lhs rhs =
    tryUnify' lhs rhs []
    where
      -- tryUnify' :: (Eq v, Eq p, Eq f) => [NormalSentence v p f] -> [NormalSentence v p f] -> [NormalSentence v p f] -> Maybe (([NormalSentence v p f], Subst v f), ([NormalSentence v p f], Subst v f))
      tryUnify' [] _ _ = Nothing
      tryUnify' (lhs:lhss) rhss lhss' =
          case tryUnify'' lhs rhss [] of
            Nothing -> tryUnify' lhss rhss (lhs:lhss')
            Just (rhss', theta1, theta2) ->
	        Just ((lhss' ++ lhss, theta1), (rhss', theta2))
      -- tryUnify'' :: (Eq v, Eq p, Eq f) => NormalSentence v p f -> [NormalSentence v p f] -> [NormalSentence v p f] ->  Maybe ([NormalSentence v p f], Subst v f, Subst v f)
      tryUnify'' _x [] _ = Nothing
      tryUnify'' x (rhs:rhss) rhss' =
          case unify x rhs of
            Nothing -> tryUnify'' x rhss (rhs:rhss')
            Just (theta1, theta2) -> Just (rhss' ++ rhss, theta1, theta2)

-- |Unification: unifies two sentences.
unify :: Implicative inf clause => clause -> clause -> Maybe (Subst v term, Subst v term)
unify s1 s2 =
    unify' s1 s2 [] []
    where
      unify' (NFPredicate p1 ts1) (NFPredicate p2 ts2) theta1 theta2 =
          if p1 == p2 then
              unifyTerms ts1 ts2 theta1 theta2
          else
              Nothing
      unify' (NFEqual xt1 xt2) (NFEqual yt1 yt2) theta1 theta2 =
          case unifyTerm xt1 yt1 theta1 theta2 of
            Just (theta1',theta2') -> unifyTerm xt2 yt2 theta1' theta2'
            Nothing -> case unifyTerm xt1 yt2 theta1 theta2 of
                         Just (theta1',theta2') -> unifyTerm xt2 yt1 theta1' theta2'
                         Nothing -> Nothing
      unify' _ _ _ _ = Nothing

unifyTerm :: (Eq v, Eq f) => Term v f -> Term v f -> Subst v f -> Subst v f -> Maybe (Subst v f, Subst v f)
unifyTerm (Function f1 ts1) (Function f2 ts2) theta1 theta2 =
    if f1 == f2 then
      unifyTerms ts1 ts2 theta1 theta2
    else
      Nothing
--unifyTerm (Constant c1) (Constant c2) theta1 theta2 =
--    if c1 == c2 then
--      Just (theta1, theta2)
--    else
--      Nothing
unifyTerm (Variable v1) t2 theta1 theta2 =
    if elem v1 (map fst theta1) then
      let
        t1' = snd (head (filter (\x -> (fst x) == v1) theta1))
      in
        unifyTerm t1' t2 theta1 theta2
    else
      Just ((v1, t2):theta1, theta2)
unifyTerm t1 (Variable v2) theta1 theta2 =
    if elem v2 (map fst theta2) then
      let
        t2' = snd (head (filter (\x -> (fst x) == v2) theta2))
      in
        unifyTerm t1 t2' theta1 theta2
    else
      Just (theta1, (v2,t1):theta2)
--unifyTerm _ _ _ _  = Nothing

unifyTerms :: (Eq v, Eq f) => [Term v f] -> [Term v f] -> Subst v f -> Subst v f -> Maybe (Subst v f, Subst v f)
unifyTerms [] [] theta1 theta2 = Just (theta1, theta2)
unifyTerms (t1:ts1) (t2:ts2) theta1 theta2 =
    case (unifyTerm t1 t2 theta1 theta2) of
      Nothing                -> Nothing
      Just (theta1',theta2') -> unifyTerms ts1 ts2 theta1' theta2'
unifyTerms _ _ _ _ = Nothing

subst = undefined
updateSubst = undefined

demodulate = undefined

-- |Convert the "question" to a set of support.
getSetOfSupport :: Implicative inf formula term v p f => [inf] -> SetOfSupport inf v term
getSetOfSupport [] = []
getSetOfSupport (x:xs) = (x, getSubsts x []) : getSetOfSupport xs

getSubsts :: forall inf formula term v p f. Implicative inf formula term v p f => inf -> Subst v term -> Subst v term
getSubsts inf theta =
    getSubstSentences (pos inf) (getSubstSentences (neg inf) theta)
    where
      -- getSubstSentences :: Implicative inf formula term v p f => [formula] -> Subst v term -> Subst v term
      getSubstSentences [] theta = theta
      getSubstSentences (x:xs) theta =
          getSubstSentences xs (getSubstSentence x theta)
      -- getSubstSentence :: Implicative inf formula term v p f => formula -> Subst v term -> Subst v term
      getSubstSentence f theta =
          foldF (\ f' -> getSubstSentence f' theta)
                undefined
                undefined
                (\ t1 op t2 -> getSubstsTerm t2 (getSubstsTerm t1 theta))
                (\ _ ts -> getSubstsTerms ts theta)
                f
      -- getSubstsTerms :: Implicative inf formula term v p f => [term] -> Subst v term -> Subst v term
      getSubstsTerms [] theta = theta
      getSubstsTerms (x:xs) theta =
          getSubstsTerms xs (getSubstsTerm x theta)
      -- getSubstsTerm :: Implicative inf formula term v p f => term -> Subst v term -> Subst v term
      getSubstsTerm t theta = 
          foldT (\ v -> if elem v (map fst theta) then theta else (v, (var v)) : theta)
                (\ _ ts -> getSubstsTerms ts theta)
                t

isRenameOf :: forall inf formula term v p f. Implicative inf formula term v p f => inf -> inf -> Bool
isRenameOf inf1 inf2 = 
    (isRenameOfSentences (pos inf1) (pos inf2)) && (isRenameOfSentences (neg inf1) (neg inf2))
    where
      -- isRenameOfSentences :: Implicative inf formula term v p f => [formula] -> [formula] -> Bool
      isRenameOfSentences xs1 xs2 =
          length xs1 == length xs2 && all id (map (uncurry isRenameOfSentence) (zip xs1 xs2))
      -- isRenameOfSentence :: Implicative inf formula term v p f => formula -> formula -> Bool
      isRenameOfSentence a b =
          foldF isRenameOfNeg
                isRenameOfQuant
                isRenameOfBinOp
                isRenameOfInfixPred
                isRenameOfPredApp
                a
          where
            -- We should have a class for normal sentences
            isRenameOfNeg a' =
                foldF (isRenameOfSentence a') no3 no3 no3 no2 b
            isRenameOfQuant qop vs a' =
                foldF no1 (\ qop' vs' b' -> qop == qop' && isRenameOfSentence a' b') no3 no3 no2 b
            isRenameOfBinOp a1 op a2 =
                foldF no1 no3 (\ b1 op' b2 -> op == op' && 
                               ((isRenameOfSentence a1 b1 && isRenameOfSentence a2 b2) ||
                                False {- If op is commutative -})) no3 no2 b
            isRenameOfInfixPred a1 op a2 =
                foldF no1 no3 no3 (\ b1 op' b2 -> op == op' && isRenameOfTerm a1 b1 && isRenameOfTerm a2 b2) no2 b
            isRenameOfPredApp p ats =
                foldF no1 no3 no3 no3 (\ p' bts -> p == p' && length ats == length bts && all id (map (uncurry isRenameOfTerm) (zip ats bts))) b
      -- isRenameOfTerm :: Implicative inf formula term v p f => term -> term -> Bool
      isRenameOfTerm t1 t2 =
          foldT (isRenameOfVar) (isRenameOfFApp) t1
          where
            isRenameOfVar v1 = foldT (const True) no2 t2
            isRenameOfFApp fn1 ts1 = foldT no1 (\ fn2 ts2 -> fn1 == fn2 && length ts1 == length ts2 && all id (map (uncurry isRenameOfTerm) (zip ts1 ts2))) t2

no1 = const False
no2 = const (const False)
no3 = const (const (const False))