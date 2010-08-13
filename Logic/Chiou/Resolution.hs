{-# OPTIONS -Wall -Werror #-}

{- Resolution.hs -}
{- Charles Chiou -}

module Logic.Chiou.Resolution
    ( prove
    , getSetOfSupport
    , SetOfSupport
    , Unification
    , Subst )
    where

import Logic.Chiou.FirstOrderLogic
import Logic.Chiou.NormalForm

type Subst v term = [(v, term)]

type SetOfSupport v p f = [Unification v p f]

type Unification v p f = (ImplicativeNormalForm v p f, Subst v (Term v f))

prove :: (Eq v, Eq p, Eq f) => SetOfSupport v p f -> SetOfSupport v p f -> [ImplicativeNormalForm v p f] ->
         (Bool, SetOfSupport v p f)
prove ss1 [] _kb = (False, ss1)
prove ss1 (s:ss2) kb =
    let
      (ss', tf) = prove' s kb ss2 ss1
    in
      if tf then
        (True, (ss1 ++ [s] ++ss'))
      else
        prove (ss1 ++ [s]) ss' (fst s:kb)

prove' :: (Eq v, Eq p, Eq f) => Unification v p f -> [ImplicativeNormalForm v p f] ->
          SetOfSupport v p f -> SetOfSupport v p f -> (SetOfSupport v p f, Bool)
prove' p kb ss1 ss2 =
    let
      res1 = map (\x -> resolution p (x,[])) kb
      res2 = map (\x -> resolution (x,[]) p) kb
      dem1 = map (\e -> demodulate p (e,[])) kb
      dem2 = map (\p' -> demodulate (p',[]) p) kb
      result = getResult (ss1 ++ ss2) (res1 ++ res2 ++ dem1 ++ dem2)
    in
      case result of
        ([], _) -> (ss1, False)
        (l, tf) -> ((ss1 ++ l), tf)

getResult :: (Eq p, Eq f) => SetOfSupport v p f -> [Maybe (Unification v p f)] ->
           (SetOfSupport v p f, Bool)
getResult _ [] = ([], False)
getResult ss (Nothing:xs) = getResult ss xs
getResult ss ((Just x):xs)  =
    case x of
      ((INF [] []),_v) -> ([x], True)
      _ -> if or (map (\(e,_) -> isRenameOf (fst x) e) ss) then
             getResult ss xs
           else
             case getResult ss xs of
               (xs', tf) -> (x:xs', tf)

-- |Convert the "question" to a set of support.
getSetOfSupport :: Eq v => [ImplicativeNormalForm v p f] -> SetOfSupport v p f
getSetOfSupport [] = []
getSetOfSupport (x:xs) = (x, getSubsts x []):getSetOfSupport xs

getSubsts :: Eq v => ImplicativeNormalForm v p f -> Subst v (Term v f) -> Subst v (Term v f)
getSubsts (INF lhs rhs) theta =
    let
      theta' = getSubstSentences lhs theta
      theta'' = getSubstSentences rhs theta'
    in
      theta''

getSubstSentences :: Eq v => [NormalSentence v p f] -> Subst v (Term v f) -> Subst v (Term v f)
getSubstSentences [] theta = theta
getSubstSentences (x:xs) theta =
    let
      theta' = getSubstSentence x theta
      theta'' = getSubstSentences xs theta'
    in
      theta''

getSubstSentence :: Eq v => NormalSentence v p f -> Subst v (Term v f) -> Subst v (Term v f)
getSubstSentence (NFPredicate _ terms) theta = getSubstsTerms terms theta
getSubstSentence (NFNot s) theta = getSubstSentence s theta
getSubstSentence (NFEqual t1 t2) theta =
    let
      theta' = getSubstsTerm t1 theta
      theta'' = getSubstsTerm t2 theta'
    in
      theta''

getSubstsTerms :: Eq v => [Term v f] -> Subst v (Term v f) -> Subst v (Term v f)
getSubstsTerms [] theta = theta
getSubstsTerms (x:xs) theta =
    let
      theta' = getSubstsTerm x theta
      theta'' = getSubstsTerms xs theta'
    in
      theta''

getSubstsTerm :: Eq v => Term v f -> Subst v (Term v f) -> Subst v (Term v f)
getSubstsTerm (Function _f terms) theta = getSubstsTerms terms theta
getSubstsTerm (Variable v) theta =
    if elem v (map fst theta) then
      theta
    else
      (v, (Variable v)):theta
--getSubstsTerm _ theta = theta

isRenameOf :: (Eq p, Eq f) => ImplicativeNormalForm v p f -> ImplicativeNormalForm v p f -> Bool
isRenameOf (INF lhs1 rhs1) (INF lhs2 rhs2) =
    (isRenameOfSentences lhs1 lhs2) && (isRenameOfSentences rhs1 rhs2)

isRenameOfSentences :: (Eq p, Eq f) => [NormalSentence v p f] -> [NormalSentence v p f] -> Bool
isRenameOfSentences xs1 xs2 =
    if length xs1 == length xs2 then
      let
        nsTuples = zip xs1 xs2
      in
        foldl (&&) True (map (\(s1, s2) -> isRenameOfSentence s1 s2) nsTuples)
    else
      False

isRenameOfSentence :: (Eq p, Eq f) => NormalSentence v p f -> NormalSentence v p f -> Bool
isRenameOfSentence (NFPredicate p1 ts1) (NFPredicate p2 ts2) =
    (p1 == p2) && (isRenameOfTerms ts1 ts2)
isRenameOfSentence (NFEqual l1 r1) (NFEqual l2 r2) =
    (isRenameOfTerm l1 l2) && (isRenameOfTerm r1 r2)
isRenameOfSentence _ _ = False

isRenameOfTerm :: Eq f => Term v f -> Term v f -> Bool
isRenameOfTerm (Function f1 t1) (Function f2 t2) =
    (f1 == f2) && (isRenameOfTerms t1 t2)
-- isRenameOfTerm (Constant c1) (Constant c2) =
--     c1 == c2
isRenameOfTerm (Variable _v1) (Variable _v2) = True
isRenameOfTerm _ _ = False

isRenameOfTerms :: Eq f => [Term v f] -> [Term v f] -> Bool
isRenameOfTerms ts1 ts2 =
    if length ts1 == length ts2 then
      let
        tsTuples = zip ts1 ts2
      in
        foldl (&&) True (map (\(t1, t2) -> isRenameOfTerm t1 t2) tsTuples)
    else
      False

resolution :: (Eq v, Eq p, Eq f) => Unification v p f -> Unification v p f -> Maybe (Unification v p f)
resolution ((INF lhs1 rhs1), theta1) ((INF lhs2 rhs2), theta2) =
    let
      unifyResult = tryUnify rhs1 lhs2
    in
      case unifyResult of
        Just ((rhs1', theta1'), (lhs2', theta2')) ->
            let
              lhs'' = map (\s -> subst s theta1') lhs1 ++
                      map (\s -> subst s theta2') lhs2'
              rhs'' = map (\s -> subst s theta1') rhs1' ++
                      map (\s -> subst s theta2') rhs2
              theta = updateSubst theta1 theta1' ++
		      updateSubst theta2 theta2'
            in
              Just ((INF lhs'' rhs''), theta)
        Nothing -> Nothing

demodulate :: (Eq v, Eq f) => Unification v p f -> Unification v p f -> Maybe (Unification v p f)
demodulate (INF [] [NFEqual t1 t2], theta1) (INF lhs2 rhs2, theta2) =
    case findUnify t1 t2 (lhs2 ++ rhs2) of
      Just ((t1', t2'), theta1', theta2') ->
          let
            substLhs2 = map (\x -> subst x theta2') lhs2
            substRhs2 = map (\x -> subst x theta2') rhs2
            lhs = map (\x -> replaceTerm x (t1', t2')) substLhs2
            rhs = map (\x -> replaceTerm x (t1', t2')) substRhs2
            theta = updateSubst theta1 theta1' ++
		    updateSubst theta2 theta2'
          in
            Just (INF lhs rhs, theta)
      Nothing        -> Nothing
demodulate _ _ = Nothing

-- |Unification: unifies two sentences.
unify :: (Eq v, Eq p, Eq f) => NormalSentence v p f -> NormalSentence v p f -> Maybe (Subst v (Term v f), Subst v (Term v f))
unify s1 s2 = unify' s1 s2 [] []

unify' :: (Eq v, Eq p, Eq f) => NormalSentence v p f -> NormalSentence v p f -> Subst v (Term v f) -> Subst v (Term v f) ->
          Maybe (Subst v (Term v f), Subst v (Term v f))
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

unifyTerm :: (Eq v, Eq f) => Term v f -> Term v f -> Subst v (Term v f) -> Subst v (Term v f) -> Maybe (Subst v (Term v f), Subst v (Term v f))
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

unifyTerms :: (Eq v, Eq f) => [Term v f] -> [Term v f] -> Subst v (Term v f) -> Subst v (Term v f) -> Maybe (Subst v (Term v f), Subst v (Term v f))
unifyTerms [] [] theta1 theta2 = Just (theta1, theta2)
unifyTerms (t1:ts1) (t2:ts2) theta1 theta2 =
    case (unifyTerm t1 t2 theta1 theta2) of
      Nothing                -> Nothing
      Just (theta1',theta2') -> unifyTerms ts1 ts2 theta1' theta2'
unifyTerms _ _ _ _ = Nothing

tryUnify :: (Eq v, Eq p, Eq f) => [NormalSentence v p f] -> [NormalSentence v p f] ->
	    Maybe (([NormalSentence v p f], Subst v (Term v f)), ([NormalSentence v p f], Subst v (Term v f)))
tryUnify lhs rhs = tryUnify' lhs rhs []

tryUnify' :: (Eq v, Eq p, Eq f) => [NormalSentence v p f] -> [NormalSentence v p f] -> [NormalSentence v p f] -> 
             Maybe (([NormalSentence v p f], Subst v (Term v f)), ([NormalSentence v p f], Subst v (Term v f)))
tryUnify' [] _ _ = Nothing
tryUnify' (lhs:lhss) rhss lhss' =
    case tryUnify'' lhs rhss [] of
      Nothing -> tryUnify' lhss rhss (lhs:lhss')
      Just (rhss', theta1, theta2) ->
	Just ((lhss' ++ lhss, theta1), (rhss', theta2))

tryUnify'' :: (Eq v, Eq p, Eq f) => NormalSentence v p f -> [NormalSentence v p f] -> [NormalSentence v p f] -> 
              Maybe ([NormalSentence v p f], Subst v (Term v f), Subst v (Term v f))
tryUnify'' _x [] _ = Nothing
tryUnify'' x (rhs:rhss) rhss' =
    case unify x rhs of
      Nothing -> tryUnify'' x rhss (rhs:rhss')
      Just (theta1, theta2) -> Just (rhss' ++ rhss, theta1, theta2)

findUnify :: (Eq v, Eq f) => Term v f -> Term v f -> [NormalSentence v p f] ->
	     Maybe ((Term v f, Term v f), Subst v (Term v f), Subst v (Term v f))
findUnify tl tr s =
    let
      terms = foldl (++) [] (map getTerms s)
      unifiedTerms' = map (\t -> unifyTerm tl t [] []) terms
      unifiedTerms = filter (\t -> t /= Nothing) unifiedTerms'
    in
     case unifiedTerms of
       [] -> Nothing
       (Just (theta1, theta2)):_ ->
	 Just ((substTerm tl theta1, substTerm tr theta1), theta1, theta2)
       (Nothing:_) -> error "findUnify"

getTerms :: NormalSentence v p f -> [Term v f]
getTerms (NFPredicate _p ts) = getTerms' ts
getTerms (NFEqual t1 t2)  = getTerms' [t1] ++ getTerms' [t2]
getTerms _ = []

getTerms' :: [Term v f] -> [Term v f]
getTerms' [] = []
getTerms' ((Function f fts):ts) =
    let
      fterms = getTerms' fts ++ getTerms' ts
    in
      (Function f fts):fterms
getTerms' (t:ts) = t:(getTerms' ts)

replaceTerm :: (Eq v, Eq f) => NormalSentence v p f -> (Term v f, Term v f) -> NormalSentence v p f
replaceTerm (NFPredicate p ts) (tl', tr') =
    NFPredicate p (map (\t -> replaceTerm' t (tl', tr')) ts)
replaceTerm (NFEqual tr tl) (tl', tr') =
    NFEqual (replaceTerm' tl (tl', tr')) (replaceTerm' tr (tl', tr'))
replaceTerm _ _ = error "error in replaceTerm"

replaceTerm' :: (Eq v, Eq f) => Term v f -> (Term v f, Term v f) -> Term v f
replaceTerm' t (tl, tr) =
    if t == tl then
      tr
    else
      case t of
        (Function f ts) -> Function f (map (\t' -> replaceTerm' t' (tl, tr)) ts)
        _  -> t

subst :: Eq v => NormalSentence v p f -> Subst v (Term v f) -> NormalSentence v p f
subst (NFPredicate p ts) theta = NFPredicate p (substTerms ts theta)
subst (NFEqual t1 t2) theta = NFEqual (substTerm t1 theta) (substTerm t2 theta)
subst s _ = s

substTerm :: Eq v => Term v f -> Subst v (Term v f) -> Term v f
substTerm (Function f ts) theta = Function f (substTerms ts theta)

substTerm (Variable v) ((sv,st):xs) =
    if v == sv then
      st
    else
      substTerm (Variable v) xs
substTerm t _ = t

substTerms :: Eq v => [Term v f] -> Subst v (Term v f) -> [Term v f]
substTerms ts theta = map (\t -> substTerm t theta) ts

updateSubst :: Eq v => Subst v (Term v f) -> Subst v (Term v f) -> Subst v (Term v f)
updateSubst [] _ = []
updateSubst ((v1,term1):xs) theta =
  case term1 of
    (Variable v') ->
        case filter (\(v,_term) -> v == v') theta of
          [] -> (v1,term1):(updateSubst xs theta)
          [(_v,term)] -> (v1,term):(updateSubst xs theta)
          _ -> error "error in updateSubst"
    _ -> (v1,term1):(updateSubst xs theta)
