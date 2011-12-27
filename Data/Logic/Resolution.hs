{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables, TypeFamilies #-}
{-# OPTIONS -Wall -Wwarn #-}

{- Resolution.hs -}
{- Charles Chiou, David Fox -}

module Data.Logic.Resolution
    ( prove
    , getSetOfSupport
    , SetOfSupport
    , Unification
    , Subst )
    where

import Data.Logic.Classes.Equals (AtomEq(foldAtomEq, zipAtomsEq, applyEq, equals))
import Data.Logic.Classes.Literal (Literal(..))
import Data.Logic.Classes.Term (Term(..))
import Data.Logic.Normal.Implicative (ImplicativeForm(INF, neg, pos))
import qualified Data.Set.Extra as S
import Data.Map (Map, empty)
import qualified Data.Map as M
import Data.Maybe (isJust)

type Subst v term = Map v term

type SetOfSupport lit v term = S.Set (Unification lit v term)

type Unification lit v term = (ImplicativeForm lit, Subst v term)

prove :: (Literal lit atom v, AtomEq atom p term, Term term v f, Ord lit, Ord term, Ord v, Eq p, Show v, Show term) =>
         Maybe Int -- ^ Recursion limit.  We continue recursing until this
                   -- becomes zero.  If it is negative it may recurse until
                   -- it overflows the stack.
      -> SetOfSupport lit v term
      -> SetOfSupport lit v term
      -> S.Set (ImplicativeForm lit)
      -> (Bool, SetOfSupport lit v term)
prove (Just 0) ss1 _ _ = (False, ss1)
prove limit ss1 ss2' kb  =
    case S.minView ss2' of
      Nothing -> (False, ss1)
      Just (s, ss2) ->
          case prove' s kb ss2 ss1 of
            (ss', True) -> (True, (S.insert s (S.union ss1 ss')))
            (ss', False) -> prove (maybe Nothing (\ n -> Just (n - 1)) limit) (S.insert s ss1) ss' (S.insert (fst s) kb)
-- prove ss1 [] _kb = (False, ss1)
-- prove ss1 (s:ss2) kb =
--     let
--       (ss', tf) = prove' s kb ss2 ss1
--     in
--       if tf then
--         (True, (ss1 ++ [s] ++ss'))
--       else
--         prove (ss1 ++ [s]) ss' (fst s:kb)
prove' :: forall lit atom p f v term.
          (Literal lit atom v, AtomEq atom p term, Term term v f, Ord lit, Ord term, Ord v, Eq p) =>
          Unification lit v term -> S.Set (ImplicativeForm lit) -> SetOfSupport lit v term -> SetOfSupport lit v term -> (SetOfSupport lit v term, Bool)
prove' p kb ss1 ss2 =
    let
      res1 = S.map (\x -> resolution p (x, empty)) kb
      res2 = S.map (\x -> resolution (x, empty) p) kb
      dem1 = S.map (\e -> demodulate p (e, empty)) kb
      dem2 = S.map (\p' -> demodulate (p', empty) p) kb
      (ss', tf) = getResult (S.union ss1 ss2) (S.unions [res1, res2, dem1, dem2])
    in
      if S.null ss' then (ss1, False) else (S.union ss1 ss', tf)

getResult :: (Literal lit atom v, AtomEq atom p term, Term term v f, Ord lit, Ord term, Ord v, Eq p) =>
             SetOfSupport lit v term -> S.Set (Maybe (Unification lit v term)) -> ((SetOfSupport lit v term), Bool)
getResult ss us =
    case S.minView us of
      Nothing ->
          (S.empty, False)
      Just (Nothing, xs) ->
          getResult ss xs
      Just ((Just x@(inf, _v)), xs) ->
          if S.null (neg inf) && S.null (pos inf)
          then (S.singleton x, True)
          else if S.any id (S.map (\(e,_) -> isRenameOf (fst x) e) ss)
               then getResult ss xs
               else let (xs', tf) = getResult ss xs in (S.insert x xs', tf)
{-
getResult _ [] = (S.empty, False)
getResult ss (Nothing:xs) = getResult ss xs
getResult ss ((Just x):xs)  =
    if S.null (neg inf) && S.null (pos inf)
    then (S.singleton x, True)
    else if S.any id (S.map (\(e,_) -> isRenameOf (fst x) e) ss)
         then getResult ss xs
         else let (xs', tf) = getResult ss xs in (S.insert x xs' tf)
    where
      (inf, _v) = x
-}

-- |Convert the "question" to a set of support.
getSetOfSupport :: (Literal formula atom v, AtomEq atom p term, Term term v f, Ord formula, Ord term, Ord v) =>
                   S.Set (ImplicativeForm formula) -> S.Set (ImplicativeForm formula, Subst v term)
getSetOfSupport s = S.map (\ x -> (x, getSubsts x empty)) s

getSubsts :: (Literal formula atom v, AtomEq atom p term, Term term v f, Ord formula) =>
             ImplicativeForm formula -> Subst v term -> Subst v term
getSubsts inf theta =
    getSubstSentences (pos inf) (getSubstSentences (neg inf) theta)

getSubstSentences :: (Literal formula atom v, AtomEq atom p term, Term term v f) => S.Set formula -> Subst v term -> Subst v term
getSubstSentences xs theta = foldr getSubstSentence theta (S.toList xs)


getSubstSentence :: (Literal formula atom v, AtomEq atom p term, Term term v f)  => formula -> Subst v term -> Subst v term
getSubstSentence formula theta =
    foldLiteral
          (\ s -> getSubstSentence s theta)
          (foldAtomEq (\ _ ts -> getSubstsTerms ts theta) (\ t1 t2 -> getSubstsTerms [t1, t2] theta))
          formula

getSubstsTerms :: Term term v f => [term] -> Subst v term -> Subst v term
getSubstsTerms [] theta = theta
getSubstsTerms (x:xs) theta =
    let
      theta' = getSubstsTerm x theta
      theta'' = getSubstsTerms xs theta'
    in
      theta''

getSubstsTerm :: Term term v f => term -> Subst v term -> Subst v term
getSubstsTerm term theta =
    foldTerm (\ v -> M.insertWith (\ _ old -> old) v (vt v) theta)
             (\ _ ts -> getSubstsTerms ts theta)
             term

isRenameOf :: (Literal lit atom v, AtomEq atom p term, Term term v f, Ord lit, Eq p) =>
              ImplicativeForm lit -> ImplicativeForm lit -> Bool
isRenameOf inf1 inf2 =
    (isRenameOfSentences lhs1 lhs2) && (isRenameOfSentences rhs1 rhs2)
    where
      lhs1 = neg inf1
      rhs1 = pos inf1
      lhs2 = neg inf2
      rhs2 = pos inf2

isRenameOfSentences :: (Literal lit atom v, AtomEq atom p term, Term term v f, Eq p) => S.Set lit -> S.Set lit -> Bool
isRenameOfSentences xs1 xs2 =
    S.size xs1 == S.size xs2 && all (uncurry isRenameOfSentence) (zip (S.toList xs1) (S.toList xs2))

isRenameOfSentence :: forall formula atom term v p f. (Literal formula atom v, AtomEq atom p term, Term term v f, Eq p) => formula -> formula -> Bool
isRenameOfSentence f1 f2 =
    maybe False id $
    zipLiterals (\ _ _ -> Just False) p f1 f2
    where p :: atom -> atom -> Maybe Bool
          p = zipAtomsEq (\ p1 ts1 p2 ts2 -> Just (p1 == p2 && isRenameOfTerms ts1 ts2))
                         (\ t1l t1r t2l t2r -> Just (isRenameOfTerm t1l t2l && isRenameOfTerm t1r t2r))

isRenameOfTerm :: Term term v f => term -> term -> Bool
isRenameOfTerm t1 t2 =
    maybe False id $
    zipTerms (\ _ _ -> Just True)
             (\ f1 ts1 f2 ts2 -> Just (f1 == f2 && isRenameOfTerms ts1 ts2))
             t1 t2

isRenameOfTerms :: Term term v f => [term] -> [term] -> Bool
isRenameOfTerms ts1 ts2 =
    if length ts1 == length ts2 then
      let
        tsTuples = zip ts1 ts2
      in
        foldl (&&) True (map (\(t1, t2) -> isRenameOfTerm t1 t2) tsTuples)
    else
      False

resolution :: forall lit atom p f term v. (Literal lit atom v, AtomEq atom p term, Term term v f, Eq lit, Ord lit, Eq term, Ord v, Eq p) =>
             (ImplicativeForm lit, Subst v term) -> (ImplicativeForm lit, Subst v term) -> Maybe (ImplicativeForm lit, Map v term)
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
              lhs'' = S.union (S.catMaybes $ S.map (\s -> subst s theta1') lhs1)
                              (S.catMaybes $ S.map (\s -> subst s theta2') lhs2')
              rhs'' = S.union (S.catMaybes $ S.map (\s -> subst s theta1') rhs1')
                              (S.catMaybes $ S.map (\s -> subst s theta2') rhs2)
              theta = M.unionWith (\ l _r -> l) (updateSubst theta1 theta1') (updateSubst theta2 theta2')
            in
              Just (INF lhs'' rhs'', theta)
        Nothing -> Nothing
    where
      tryUnify :: (Literal formula atom v, Ord formula) =>
                  S.Set formula -> S.Set formula -> Maybe ((S.Set formula, Subst v term), (S.Set formula, Subst v term))
      tryUnify lhs rhs = tryUnify' lhs rhs S.empty
                         
      tryUnify' :: (Literal formula atom v, Ord formula) =>
                   S.Set formula -> S.Set formula -> S.Set formula -> Maybe ((S.Set formula, Subst v term), (S.Set formula, Subst v term))
      tryUnify' lhss _ _ | S.null lhss = Nothing
      tryUnify' lhss'' rhss lhss' =
          let (lhs, lhss) = S.deleteFindMin lhss'' in
          case tryUnify'' lhs rhss S.empty of
            Nothing -> tryUnify' lhss rhss (S.insert lhs lhss')
            Just (rhss', theta1', theta2') ->
                Just ((S.union lhss' lhss, theta1'), (rhss', theta2'))

      tryUnify'' :: (Literal formula atom v, Ord formula) =>
                    formula -> S.Set formula -> S.Set formula -> Maybe (S.Set formula, Subst v term, Subst v term)
      tryUnify'' _x rhss _ | S.null rhss = Nothing
      tryUnify'' x rhss'' rhss' =
          let (rhs, rhss) = S.deleteFindMin rhss'' in
          case unify x rhs of
            Nothing -> tryUnify'' x rhss (S.insert rhs rhss')
            Just (theta1', theta2') -> Just (S.union rhss' rhss, theta1', theta2')

-- |Try to unify the second argument using the equality in the first.
demodulate :: (Literal lit atom v, AtomEq atom p term, Term term v f, Eq lit, Ord lit, Eq term, Ord v) =>
              (Unification lit v term) -> (Unification lit v term) -> Maybe (Unification lit v term)
demodulate (inf1, theta1) (inf2, theta2) =
    case (S.null (neg inf1), S.toList (pos inf1)) of
      (True, [lit1]) ->
          foldLiteral (\ _ -> error "demodulate") (foldAtomEq (\ _ _ -> Nothing) p) lit1
      _ -> Nothing
    where
      p t1 t2 =
          case findUnify t1 t2 (S.union lhs2 rhs2) of
            Just ((t1', t2'), theta1', theta2') ->
                let substNeg2 = S.catMaybes $ S.map (\x -> subst x theta2') lhs2
                    substPos2 = S.catMaybes $ S.map (\x -> subst x theta2') rhs2
                    lhs = S.catMaybes $ S.map (\x -> replaceTerm x (t1', t2')) substNeg2
                    rhs = S.catMaybes $ S.map (\x -> replaceTerm x (t1', t2')) substPos2
                    theta = M.unionWith (\ l _r -> l) (updateSubst theta1 theta1') (updateSubst theta2 theta2') in
                Just (INF lhs rhs, theta)
            Nothing -> Nothing
      lhs2 = neg inf2
      rhs2 = pos inf2

-- |Unification: unifies two sentences.
unify :: (Literal formula atom v, AtomEq atom p term, Term term v f, Eq p)  => formula -> formula -> Maybe (Subst v term, Subst v term)
unify s1 s2 = unify' s1 s2 empty empty

unify' :: (Literal formula atom v, AtomEq atom p term, Term term v f, Eq p) =>
          formula -> formula -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unify' f1 f2 theta1 theta2 =
    zipLiterals
         (\ _ _ -> error "unify'")
         (zipAtomsEq (\ p1 ts1 p2 ts2 -> if p1 == p2 then unifyTerms ts1 ts2 theta1 theta2 else Nothing)
                     (\ l1 r1 l2 r2 -> unifyTerms [l1, r1] [l2, r2] theta1 theta2))
         f1 f2

unifyTerm :: Term term v f => term -> term -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unifyTerm t1 t2 theta1 theta2 =
    foldTerm
          (\ v1 ->
               maybe (if vt v1 == t2 then Nothing else Just (M.insert v1 t2 theta1, theta2))
                     (\ t1' -> unifyTerm t1' t2 theta1 theta2)
                     (M.lookup v1 theta1))
          (\ f1 ts1 ->
               foldTerm (\ v2 -> maybe (Just (theta1, M.insert v2 t1 theta2))
                                 (\ t2' -> unifyTerm t1 t2' theta1 theta2)
                                 (M.lookup v2 theta2))
                        (\ f2 ts2 -> if f1 == f2
                                     then unifyTerms ts1 ts2 theta1 theta2
                                     else Nothing)
                        t2)
          t1

unifyTerms :: Term term v f =>
              [term] -> [term] -> Subst v term -> Subst v term -> Maybe (Subst v term, Subst v term)
unifyTerms [] [] theta1 theta2 = Just (theta1, theta2)
unifyTerms (t1:ts1) (t2:ts2) theta1 theta2 =
    case (unifyTerm t1 t2 theta1 theta2) of
      Nothing                -> Nothing
      Just (theta1',theta2') -> unifyTerms ts1 ts2 theta1' theta2'
unifyTerms _ _ _ _ = Nothing

findUnify :: forall formula atom term v p f. (Literal formula atom v, AtomEq atom p term, Term term v f) =>
             term -> term -> S.Set formula -> Maybe ((term, term), Subst v term, Subst v term)
findUnify tl tr s =
    let
      terms = concatMap (foldLiteral (\ (_ :: formula) -> error "getTerms") p) (S.toList s)
      unifiedTerms' = map (\t -> unifyTerm tl t empty empty) terms
      unifiedTerms = filter isJust unifiedTerms'
    in
     case unifiedTerms of
       [] -> Nothing
       (Just (theta1, theta2)):_ ->
         Just ((substTerm tl theta1, substTerm tr theta1), theta1, theta2)
       (Nothing:_) -> error "findUnify"
    where
      -- getTerms formula = foldLiteral (\ _ -> error "getTerms") p formula
      p :: atom -> [term]
      p = foldAtomEq (\ _ ts -> concatMap getTerms' ts) (\ t1 t2 -> getTerms' t1 ++ getTerms' t2)
      getTerms' :: term -> [term]
      getTerms' t = foldTerm (\ v -> [vt v]) (\ f ts -> fApp f ts : concatMap getTerms' ts) t

{-
getTerms :: Literal formula atom v => formula -> [term]
getTerms formula =
    foldLiteral (\ _ -> error "getTerms") p formula
    where
      getTerms' t = foldT (\ v -> [vt v]) (\ f ts -> fApp f ts : concatMap getTerms' ts) t
      p (Equal t1 t2) = getTerms' t1 ++ getTerms' t2
      p (Apply _ ts) = concatMap getTerms' ts
-}

replaceTerm :: (Literal lit atom v, AtomEq atom p term, Term term v f, Eq term) => lit -> (term, term) -> Maybe lit
replaceTerm formula (tl', tr') =
    foldLiteral
          (\ _ -> error "error in replaceTerm")
          (foldAtomEq (\ p ts -> Just (atomic (applyEq p (map (\ t -> replaceTerm' t) ts))))
                      (\ t1 t2 -> 
                           let t1' = replaceTerm' t1
                               t2' = replaceTerm' t2 in
                           if t1' == t2' then Nothing else Just (atomic (t1' `equals` t2'))))
          formula
    where
      replaceTerm' t =
          if termEq t tl'
          then tr'
          else foldTerm vt (\ f ts -> fApp f (map replaceTerm' ts)) t
      termEq t1 t2 =
          maybe False id (zipTerms (\ v1 v2 -> Just (v1 == v2)) (\ f1 ts1 f2 ts2 -> Just (f1 == f2 && length ts1 == length ts2 && all (uncurry termEq) (zip ts1 ts2))) t1 t2)

subst :: (Literal formula atom v, AtomEq atom p term, Term term v f, Eq term) => formula -> Subst v term -> Maybe formula
subst formula theta =
    foldLiteral
          (\ _ -> Just formula)
          (foldAtomEq (\ p ts -> Just (atomic (applyEq p (substTerms ts theta))))
                      (\ t1 t2 ->
                           let t1' = substTerm t1 theta
                               t2' = substTerm t2 theta in
                           if t1' == t2' then Nothing else Just (atomic (t1' `equals` t2'))))
          formula

substTerm :: Term term v f => term -> Subst v term -> term
substTerm term theta =
    foldTerm (\ v -> maybe term id (M.lookup v theta))
             (\ f ts -> fApp f (substTerms ts theta))
             term

substTerms :: Term term v f => [term] -> Subst v term -> [term]
substTerms ts theta = map (\t -> substTerm t theta) ts

updateSubst :: Term term v f => Subst v term -> Subst v term -> Subst v term
updateSubst theta1 theta2 = M.union theta1 (M.intersection theta1 theta2)
-- This is what was in the original code, which behaves slightly differently
--updateSubst theta1 _ | M.null theta1 = M.empty
--updateSubst theta1 theta2 = M.unionWith (\ _ term2 -> term2) theta1 theta2
