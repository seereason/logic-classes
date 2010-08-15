{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS -Wall -Wwarn #-}

{- Resolution.hs -}
{- Charles Chiou -}

module Logic.Resolution
    ( prove
    , getSetOfSupport
    , SetOfSupport
    , Unification
    , Subst )
    where

import qualified Logic.FirstOrder as Logic
import Logic.Implicative (Implicative(..))

type Subst v term = [(v, term)]

type SetOfSupport inf v term = [Unification inf v term]

type Unification inf v term = (inf, Subst v term)

prove :: (Implicative inf lit, Eq term, Logic.FirstOrderLogic lit term v p f) =>
         (SetOfSupport inf v term) -> (SetOfSupport inf v term) -> [inf] -> (Bool, (SetOfSupport inf v term))
prove ss1 [] _kb = (False, ss1)
prove ss1 (s:ss2) kb =
    let
      (ss', tf) = prove' s kb ss2 ss1
    in
      if tf then
        (True, (ss1 ++ [s] ++ss'))
      else
        prove (ss1 ++ [s]) ss' (fst s:kb)

prove' :: (Implicative inf lit, Eq term, Logic.FirstOrderLogic lit term v p f) =>
          (Unification inf v term) -> [inf] -> (SetOfSupport inf v term) -> (SetOfSupport inf v term) -> ((SetOfSupport inf v term), Bool)
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

getResult :: (Logic.FirstOrderLogic lit term v p f, Implicative inf lit) =>
             (SetOfSupport inf v term) -> [Maybe (Unification inf v term)] -> ((SetOfSupport inf v term), Bool)
getResult _ [] = ([], False)
getResult ss (Nothing:xs) = getResult ss xs
getResult ss ((Just x):xs)  =
    case (neg inf, pos inf) of
      ([], []) -> ([x], True)
      _ -> if or (map (\(e,_) -> isRenameOf (fst x) e) ss) then
             getResult ss xs
           else
             case getResult ss xs of
               (xs', tf) -> (x:xs', tf)
    where
      (inf, _v) = x

-- |Convert the "question" to a set of support.
getSetOfSupport :: (Implicative t formula, Logic.FirstOrderLogic formula term v p f) =>
                   [t] -> [(t, Subst v term)]
getSetOfSupport [] = []
getSetOfSupport (x:xs) = (x, getSubsts x []):getSetOfSupport xs

getSubsts :: (Implicative inf formula, Logic.FirstOrderLogic formula term v p f) =>
             inf -> Subst v term -> Subst v term
getSubsts inf theta =
    getSubstSentences (pos inf) (getSubstSentences (neg inf) theta)

getSubstSentences :: Logic.FirstOrderLogic formula term v p f => [formula] -> Subst v term -> Subst v term
getSubstSentences [] theta = theta
getSubstSentences (x:xs) theta =
    let
      theta' = getSubstSentence x theta
      theta'' = getSubstSentences xs theta'
    in
      theta''


getSubstSentence :: Logic.FirstOrderLogic formula term v p f => formula -> Subst v term -> Subst v term
getSubstSentence formula theta =
    Logic.foldF (\ s -> getSubstSentence s theta)
                (\ _ _ _ -> error "getSubstSentence")
                (\ _ _ _ -> error "getSubstSentence")
                (\ t1 op t2 -> case op of
                                 (Logic.:=:) -> getSubstsTerm t2 (getSubstsTerm t1 theta)
                                 _ -> error "getSubstSentence")
                (\ _ ts -> getSubstsTerms ts theta)
                formula

getSubstsTerms :: Logic.Term term v f => [term] -> Subst v term -> Subst v term
getSubstsTerms [] theta = theta
getSubstsTerms (x:xs) theta =
    let
      theta' = getSubstsTerm x theta
      theta'' = getSubstsTerms xs theta'
    in
      theta''

getSubstsTerm :: Logic.Term term v f => term -> Subst v term -> Subst v term
getSubstsTerm term theta =
    Logic.foldT (\ v -> if elem v (map fst theta)
                        then theta
                        else (v, Logic.var v) : theta)
                (\ _ ts -> getSubstsTerms ts theta)
                term

isRenameOf :: (Implicative inf lit, Logic.FirstOrderLogic lit term v p f) =>
              inf -> inf -> Bool
isRenameOf inf1 inf2 =
    (isRenameOfSentences lhs1 lhs2) && (isRenameOfSentences rhs1 rhs2)
    where
      lhs1 = neg inf1
      rhs1 = pos inf1
      lhs2 = neg inf2
      rhs2 = pos inf2

isRenameOfSentences :: Logic.FirstOrderLogic a term v p f => [a] -> [a] -> Bool
isRenameOfSentences xs1 xs2 =
    if length xs1 == length xs2 then
      let
        nsTuples = zip xs1 xs2
      in
        foldl (&&) True (map (\(s1, s2) -> isRenameOfSentence s1 s2) nsTuples)
    else
      False

isRenameOfSentence :: Logic.FirstOrderLogic formula term v p f => formula -> formula -> Bool
isRenameOfSentence f1 f2 =
    maybe False id $
    Logic.zipF (\ _ _ -> Nothing)
               (\ _ _ _ _ _ _ -> Nothing)
               (\ _ _ _ _ _ _ -> Nothing)
               (\ t1l op1 t1r t2l op2 t2r ->
                    if op1 == (Logic.:=:) && op2 == (Logic.:=:)
                    then Just (isRenameOfTerm t1l t2l && isRenameOfTerm t1r t2r)
                                {- || (isRenameOfTerm t1l t2r && isRenameOfTerm l1r t2l) -}
                    else Nothing)
               (\ p1 ts1 p2 ts2 -> Just (p1 == p2 && isRenameOfTerms ts1 ts2))
               f1 f2

isRenameOfTerm :: Logic.Term term v f => term -> term -> Bool
isRenameOfTerm t1 t2 =
    maybe False id $
    Logic.zipT (\ _ _ -> Just True)
               (\ f1 ts1 f2 ts2 -> Just (f1 == f2 && isRenameOfTerms ts1 ts2))
               t1 t2

isRenameOfTerms :: Logic.Term term v f => [term] -> [term] -> Bool
isRenameOfTerms ts1 ts2 =
    if length ts1 == length ts2 then
      let
        tsTuples = zip ts1 ts2
      in
        foldl (&&) True (map (\(t1, t2) -> isRenameOfTerm t1 t2) tsTuples)
    else
      False

resolution :: (Logic.FirstOrderLogic lit term v p f, Implicative inf lit) =>
              (Unification inf v term) -> (Unification inf v term) -> Maybe (Unification inf v term)
resolution (inf1, theta1) (inf2, theta2) =
    let
        lhs1 = neg inf1
        rhs1 = pos inf1
        lhs2 = neg inf2
        rhs2 = pos inf2
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
              Just (makeINF lhs'' rhs'', theta)
        Nothing -> Nothing

demodulate :: (Eq term, Implicative inf lit, Logic.FirstOrderLogic lit term v p f) =>
              (Unification inf v term) -> (Unification inf v term) -> Maybe (Unification inf v term)
demodulate (inf1, theta1) (inf2, theta2) =
    let lhs2 = neg inf2
        rhs2 = pos inf2 in
    case (neg inf1, pos inf1) of
      ([], [lit1]) ->
          Logic.foldF (\ _ -> error "demodulate")
                      (\ _ _ _ -> error "demodulate")
                      (\ _ _ _ -> error "demodulate")
                      (\ t1 op t2 -> case op of
                                       (Logic.:=:) ->
                                           case findUnify t1 t2 (lhs2 ++ rhs2) of
                                             Just ((t1', t2'), theta1', theta2') ->
                                                 let substLhs2 = map (\x -> subst x theta2') lhs2
                                                     substRhs2 = map (\x -> subst x theta2') rhs2
                                                     lhs = map (\x -> replaceTerm x (t1', t2')) substLhs2
                                                     rhs = map (\x -> replaceTerm x (t1', t2')) substRhs2
                                                     theta = updateSubst theta1 theta1' ++
		                                             updateSubst theta2 theta2' in
                                                 Just (makeINF lhs rhs, theta)
                                             Nothing -> Nothing
                                       _ -> Nothing)
                      (\ _ _ -> Nothing)
                      lit1
      _ -> Nothing
-- |Unification: unifies two sentences.
unify :: Logic.FirstOrderLogic formula term v p f => formula -> formula -> Maybe (Subst v term, Subst v term)
unify s1 s2 = unify' s1 s2 [] []

unify' :: Logic.FirstOrderLogic formula term v p f =>
          formula -> formula -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unify' f1 f2 theta1 theta2 =
    Logic.zipF (\ _ _ -> error "unify'")
               (\ _ _ _ _ _ _ -> error "unify'")
               (\ _ _ _ _ _ _ -> error "unify'")
               (\ t1l op1 t1r t2l op2 t2r ->
                    if op1 == op2
                    then case unifyTerm t1l t2l theta1 theta2 of
                           Just (theta1', theta2') -> unifyTerm t1r t2r theta1' theta2'
                           Nothing -> case unifyTerm t1l t2r theta1 theta2 of
                                        Just (theta1', theta2') -> unifyTerm t1r t2l theta1' theta2'
                                        Nothing -> Nothing
                    else error "unify'")
               (\ p1 ts1 p2 ts2 -> if p1 == p2 then unifyTerms ts1 ts2 theta1 theta2 else Nothing)
               f1 f2

unifyTerm :: Logic.FirstOrderLogic formula term v p f => term -> term -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unifyTerm t1 t2 theta1 theta2 =
    Logic.foldT (\ v1 ->
                     if elem v1 (map fst theta1)
                     then let t1' = snd (head (filter (\ x -> fst x == v1) theta1)) in
                          unifyTerm t1' t2 theta1 theta2
                     else Just ((v1, t2) : theta1, theta2))
                (\ f1 ts1 ->
                     Logic.foldT (\ v2 -> if elem v2 (map fst theta2)
                                          then let t2' = snd (head (filter (\ x -> fst x == v2) theta2)) in
                                               unifyTerm t1 t2' theta1 theta2
                                          else Just (theta1, (v2,t1) : theta2))
                                 (\ f2 ts2 -> if f1 == f2
                                              then unifyTerms ts1 ts2 theta1 theta2
                                              else Nothing)
                                 t2)
                t1

unifyTerms :: Logic.FirstOrderLogic formula term v p f =>
              [term] -> [term] -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unifyTerms [] [] theta1 theta2 = Just (theta1, theta2)
unifyTerms (t1:ts1) (t2:ts2) theta1 theta2 =
    case (unifyTerm t1 t2 theta1 theta2) of
      Nothing                -> Nothing
      Just (theta1',theta2') -> unifyTerms ts1 ts2 theta1' theta2'
unifyTerms _ _ _ _ = Nothing

tryUnify :: Logic.FirstOrderLogic formula term v p f =>
            [formula] -> [formula] -> Maybe (([formula], Subst v term), ([formula], Subst v term))
tryUnify lhs rhs = tryUnify' lhs rhs []

tryUnify' :: Logic.FirstOrderLogic formula term v p f =>
             [formula] -> [formula] -> [formula] -> Maybe (([formula], Subst v term), ([formula], Subst v term))
tryUnify' [] _ _ = Nothing
tryUnify' (lhs:lhss) rhss lhss' =
    case tryUnify'' lhs rhss [] of
      Nothing -> tryUnify' lhss rhss (lhs:lhss')
      Just (rhss', theta1, theta2) ->
	Just ((lhss' ++ lhss, theta1), (rhss', theta2))

tryUnify'' :: Logic.FirstOrderLogic formula term v p f =>
              formula -> [formula] -> [formula] -> Maybe ([formula], Subst v term, Subst v term)
tryUnify'' _x [] _ = Nothing
tryUnify'' x (rhs:rhss) rhss' =
    case unify x rhs of
      Nothing -> tryUnify'' x rhss (rhs:rhss')
      Just (theta1, theta2) -> Just (rhss' ++ rhss, theta1, theta2)

findUnify :: (Logic.FirstOrderLogic formula term v p f, Eq term, Logic.Term term v f) =>
             term -> term -> [formula] -> Maybe ((term, term), Subst v term, Subst v term)
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

getTerms :: Logic.FirstOrderLogic formula term v p f => formula -> [term]
getTerms formula =
    Logic.foldF (\ _ -> error "getTerms")
                (\ _ _ _ -> error "getTerms")
                (\ _ _ _ -> error "getTerms")
                (\ t1 op t2 -> case op of
                                 (Logic.:=:) -> getTerms' t1 ++ getTerms' t2
                                 _ -> error "getTerms")
                (\ _ ts -> concatMap getTerms' ts)
                formula
    where
      getTerms' t = Logic.foldT (\ v -> [Logic.var v]) (\ f ts -> Logic.fApp f ts : concatMap getTerms' ts) t

replaceTerm :: (Eq term, Logic.FirstOrderLogic formula term v p f) => formula -> (term, term) -> formula
replaceTerm formula (tl', tr') =
    Logic.foldF (\ _ -> error "error in replaceTerm")
                (\ _ _ _ -> error "error in replaceTerm")
                (\ _ _ _ -> error "error in replaceTerm")
                (\ tl op tr -> case op of
                                 (Logic.:=:) -> replaceTerm' tl Logic..=. replaceTerm' tr
                                 _ -> error "error in replaceTerm")
                (\ p ts -> Logic.pApp p (map (\ t -> replaceTerm' t) ts))
                formula
    where
      replaceTerm' t =
          if t == tl'
          then tr'
          else Logic.foldT Logic.var (\ f ts -> Logic.fApp f (map replaceTerm' ts)) t

subst :: Logic.FirstOrderLogic formula term v p f => formula -> Subst v term -> formula
subst formula theta =
    Logic.foldF (\ _ -> formula)
                (error "subst")
                (error "subst")
                (\ t1 op t2 -> Logic.infixPred (substTerm t1 theta) op (substTerm t2 theta))
                (\ p ts -> Logic.pApp p (substTerms ts theta))
                formula

substTerm :: Logic.Term term v f => term -> Subst v term -> term
substTerm term theta =
    Logic.foldT (\ v -> case theta of
                          ((sv,st):xs) -> if v == sv then st else substTerm term xs
                          _ -> term)
                (\ f ts -> Logic.fApp f (substTerms ts theta))
                term

substTerms :: Logic.Term term v f => [term] -> Subst v term -> [term]
substTerms ts theta = map (\t -> substTerm t theta) ts

updateSubst :: Logic.Term term v f => Subst v term -> Subst v term -> Subst v term
updateSubst [] _ = []
updateSubst ((v1,term1):xs) theta =
    Logic.foldT ( \ v' -> 
                      case filter (\(v,_term) -> v == v') theta of
                        [] -> (v1,term1):(updateSubst xs theta)
                        [(_,term)] -> (v1,term):(updateSubst xs theta)
                        _ -> error "error in updateSubst")
                ( \ _ _ -> (v1,term1):(updateSubst xs theta))
                term1
