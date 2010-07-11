{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, UndecidableInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing #-}

{- NormalForm.hs -}
{- Charles Chiou -}

{- Convert sentences into:
 - Conjunctive Normal Form (CNF) or
 - Implicative Normal Form (INF)
 -}

module Logic.Chiou.NormalForm
    ( ConjunctiveNormalForm(..)
    , ImplicativeNormalForm(..)
    , NormalSentence(..)
    , toCNF, toCNFSentence, showCNFDerivation
    , toINF, toINFSentence, showINFDerivation
    , distributeAndOverOr
    ) where

import qualified Data.Set as S
import Logic.Chiou.FirstOrderLogic (Sentence(..), Term(..), Connective(..), Quantifier(..))
import Logic.FirstOrder -- (Skolem(..), Boolean(..), {-, FirstOrderLogic, convertPred-} quant, infixPred, pApp)
import Logic.Implicative (Literal(..), Implicative(..))

data ConjunctiveNormalForm v p f =
    CNF [NormalSentence v p f]
    deriving (Eq)

data ImplicativeNormalForm v p f
    = INF [NormalSentence v p f] [NormalSentence v p f]
    deriving (Eq)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [Term v f]
    | NFEqual (Term v f) (Term v f)
    deriving (Eq, Ord)

instance Boolean p => Literal (NormalSentence v p f) (Term v f) p where
    litEqual t1 t2 = NFEqual t1 t2
    litPredicate p ts = NFPredicate p ts
    litFold equal predicate l =
        case l of
          NFEqual t1 t2 -> equal t1 t2
          NFPredicate p ts -> predicate p ts
          _ -> error "Logic.Chiou.NormalForm: Invalid NormalSentence"

instance (Ord v, Ord p, Boolean p, Ord f, Skolem f) => Implicative (ImplicativeNormalForm v p f) (NormalSentence v p f) (Term v f) p where
    neg (INF x _) = S.fromList x
    pos (INF _ x) = S.fromList x

toCNF :: (Eq v, Eq p, Eq f, Skolem f) => Sentence v p f -> ConjunctiveNormalForm v p f
toCNF s = CNF (normalize (toCNFSentence s))

toCNFSentence :: (Eq v, Eq p, Eq f, Skolem f) => Sentence v p f -> Sentence v p f
toCNFSentence s0 = let
 		     s1 = eliminateImplication s0
		     s2 = moveNotInwards s1
		     s3 = standardizeVariables s2
		     s4 = moveQuantifiersLeft s3
		     s5 = skolemize s4
		     s6 = distributeAndOverOr s5
		   in
		     s6

showCNFDerivation :: (Show (Sentence v p f), Eq v, Eq p, Eq f, Skolem f, Show v, Show p, Show f) => Sentence v p f -> String
showCNFDerivation s0 = let
		         s1 = eliminateImplication s0
			 s2 = moveNotInwards s1
			 s3 = standardizeVariables s2
			 s4 = moveQuantifiersLeft s3
			 s5 = skolemize s4
			 s6 = distributeAndOverOr s5
		       in
		         "Input sentence:\t" ++
			 (show s0 ++ "\n") ++
			 "Eliminate implication:\t" ++
			 (show s1 ++ "\n") ++
			 "Move NOT inwards:\t" ++
			 (show s2 ++ "\n") ++
			 "Standardize Variables:\t" ++
			 (show s3 ++ "\n") ++
			 "Move quantifiers left:\t" ++
			 (show s4 ++ "\n") ++
			 "Skolemize variables:\t" ++
			 (show s5 ++ "\n") ++
			 "Distribute AND over OR:\t" ++
			 (show s6 ++ "\n")

toINF :: (Eq v, Eq p, Eq f, Skolem f, Boolean p) => Sentence v p f -> [ImplicativeNormalForm v p f]
toINF s =
    let
      cnf = toCNFSentence s
      cnfL = collectCnf cnf
    in
      map toINF' cnfL

toINF' :: (Eq v, Eq p, Eq f, Boolean p) => Sentence v p f -> ImplicativeNormalForm v p f
toINF' s =
    let
      norm = normalize s
      neg' = filter (\ns -> case ns of
		              (NFNot _) -> True
		              _ -> False) norm
      neg = map (\ns -> case ns of
		          (NFNot x) -> x
		          _ -> error "negative literal on LHS") neg'
      pos = filter (\ns -> case ns of
			     (NFNot _) -> False
		             _ -> True) norm
    in
      if neg == [ NFPredicate (fromBool True) [] ] then
        INF [] pos
      else
        if pos == [ NFPredicate (fromBool False) [] ] then
	  INF neg []
	else
	  INF neg pos

toINFSentence :: (Eq v, Eq p, Eq f, Skolem f, Boolean p) => Sentence v p f -> Sentence v p f
toINFSentence s0 = let
		     s1 = toCNFSentence s0
		     s2 = disjunctionToImplication s1
		   in
		     s2

showINFDerivation :: (Show (Sentence v p f), Eq v, Eq p, Eq f, Skolem f, Boolean p, Show v, Show p, Show f) => Sentence v p f -> String
showINFDerivation s0 = let
		         s1 = toCNFSentence s0
			 s2 = disjunctionToImplication s1
		       in
		         showCNFDerivation s0 ++
			 "Convert disjunctions to implications:\t" ++
			 (show s2 ++ "\n")

{-- 
   Invariants:
   P => Q           becomes       (NOT P) OR Q
   P <=> Q          becomes       ((NOT P) OR Q) AND ((NOT Q) OR P)
 -}
eliminateImplication :: Sentence v p f -> Sentence v p f
eliminateImplication (Connective s1 Imply s2) =
    Connective (Not (eliminateImplication s1)) Or (eliminateImplication s2)
eliminateImplication (Connective s1 Equiv s2) =
    let
      c1 = Connective (Not (eliminateImplication s1)) Or (eliminateImplication s2)
      c2 = Connective (Not (eliminateImplication s2)) Or (eliminateImplication s1)
    in
      Connective c1 And c2

eliminateImplication (Connective s1 c s2) =
    Connective (eliminateImplication s1) c (eliminateImplication s2)
eliminateImplication (Quantifier q vs s) =
    Quantifier q vs (eliminateImplication s)
eliminateImplication (Not s) = Not (eliminateImplication s)
eliminateImplication s = s

{--
   Invariants:
   NOT (P OR Q)      becomes     (NOT P) AND (NOT Q)
   NOT (P AND Q)     becomes     (NOT P) OR (NOT Q)
   NOT (ForAll x P)  becomes     Exists x (NOT P)
   NOT (Exists x P)  becomes     ForAll x (NOT P)
   NOT (NOT P)       becomes     P
 -}
moveNotInwards :: Sentence v p f -> Sentence v p f
moveNotInwards (Connective s1 c s2) =
    Connective (moveNotInwards s1) c (moveNotInwards s2)
moveNotInwards (Quantifier q vs s) = Quantifier q vs (moveNotInwards s)
moveNotInwards (Not (Connective s1 Or s2)) =
    Connective (moveNotInwards (Not s1)) And (moveNotInwards (Not s2))
moveNotInwards (Not (Connective s1 And s2)) =
    Connective (moveNotInwards (Not s1)) Or (moveNotInwards (Not s2))
moveNotInwards (Not (Quantifier ForAll vs s)) =
    Quantifier ExistsCh vs (moveNotInwards (Not s))
moveNotInwards (Not (Quantifier ExistsCh vs s)) =
    Quantifier ForAll vs (moveNotInwards (Not s))
moveNotInwards (Not (Not s)) = moveNotInwards s
moveNotInwards (Not s) = Not (moveNotInwards s)
moveNotInwards s = s

standardizeVariables :: Sentence v p f -> Sentence v p f
standardizeVariables s = s

{--
 
 -}
moveQuantifiersLeft :: Sentence v p f -> Sentence v p f
moveQuantifiersLeft s =
    let
      (s', qs) = collectQuantifiers' s
    in 
      prependQuantifiers' (s', qs)

collectQuantifiers' :: Sentence v p f -> (Sentence v p f, [(Quantifier, [v])])
collectQuantifiers' (Not s) =
    let
      (s', qs') = collectQuantifiers' s
    in
      (Not s', qs')
collectQuantifiers' (Quantifier q vs s) =
    let
      (s', qs') = collectQuantifiers' s
    in
      (s', ((q, vs):qs'))
collectQuantifiers' (Connective s1 c s2) =
    let
      (s1', qs1') = collectQuantifiers' s1
      (s2', qs2') = collectQuantifiers' s2
    in
      (Connective s1' c s2', qs1' ++ qs2')
collectQuantifiers' s =  (s, [])

prependQuantifiers' :: (Sentence v p f, [(Quantifier, [v])]) -> Sentence v p f
prependQuantifiers' (s, []) = s
prependQuantifiers' (s, ((q, vs):qs)) = Quantifier q vs (prependQuantifiers' (s, qs))


{- 
   Invariants:
   (A AND B) OR C     becomes    (A OR C) AND (B OR C)
   A OR (B AND C)     becomes    (A OR B) AND (B OR C)
  -}
distributeDisjuncts :: (Eq f, Eq p, Eq v) => Sentence v p f -> Sentence v p f
distributeDisjuncts =
    foldFCh Not q b Equal Predicate
    where
      q op vs x = Quantifier op vs (distributeDisjuncts x)
      b f1 Or f2 = doRHS (distributeDisjuncts f1) (distributeDisjuncts f2)
      b f1 And f2 = distributeDisjuncts f1 .&. distributeDisjuncts f2
      b f1 op f2 = Connective (distributeDisjuncts f1) op (distributeDisjuncts f2)
      -- Helper function once we've seen a disjunction.  Note that it does not call itself.
      doRHS f1 f2 =
          foldFCh n' q' b' i' a' f2
          where
            n' _ = doLHS f1 f2
            -- Quick simplification, but assumes Eq formula: (p | q) & p -> p
            -- b' f3 And f4 | f1 == f3 || f1 == f4 = distributeDisjuncts f1
            b' f3 And f4 = distributeDisjuncts (distributeDisjuncts (f1 .|. f3) .&. distributeDisjuncts (f1 .|. f4))
            b' _ _ _ = doLHS f1 f2
            q' _ _ _ = doLHS f1 f2
            i' _ _ = doLHS f1 f2
            a' _ _ = doLHS f1 f2
      doLHS f1 f2 =
          foldFCh n' q' b' i' a' f1
          where
            n' _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            q' _ _ _ =  distributeDisjuncts f1 .|. distributeDisjuncts f2
            -- Quick simplification, but assumes Eq formula: p & (p | q) -> p
            -- b' f3 And f4 | f2 == f3 ||  f2 == f4 = distributeDisjuncts f2
            b' f3 And f4 = distributeDisjuncts (distributeDisjuncts (f3 .|. f2) .&. distributeDisjuncts (f4 .|. f2))
            b' _ _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            i' _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2
            a' _ _ = distributeDisjuncts f1 .|. distributeDisjuncts f2

(.&.) :: Sentence v p f -> Sentence v p f -> Sentence v p f
(.&.) a b = Connective a And b
(.|.) :: Sentence v p f -> Sentence v p f -> Sentence v p f
(.|.) a b = Connective a Or b

foldFCh :: (Sentence v p f -> r)
      -> (Quantifier -> [v] -> Sentence v p f -> r)
      -> (Sentence v p f -> Connective -> Sentence v p f -> r)
      -> (Term v f -> Term v f -> r)
      -> (p -> [Term v f] -> r)
      -> Sentence v p f
      -> r
foldFCh n q b i a formula =
    case formula of
      Not f -> n f
      Quantifier op vs f -> q op vs f
      Connective f1 op f2 -> b f1 op f2
      Equal t1 t2 -> i t1 t2
      Predicate p ts -> a p ts

distributeAndOverOr :: (Eq v, Eq p, Eq f) => Sentence v p f -> Sentence v p f
distributeAndOverOr = distributeDisjuncts

{-
distributeAndOverOr (Connective (Connective s1 And s2) Or s3) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
      s3' = distributeAndOverOr s3
    in
      distributeAndOverOr (Connective (Connective s1' Or s3') And
			              (Connective s2' Or s3'))
distributeAndOverOr (Connective s1 Or (Connective s2 And s3)) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
      s3' = distributeAndOverOr s3
    in
      distributeAndOverOr (Connective (Connective s1' Or s2') And
			              (Connective s1' Or s3'))
distributeAndOverOr (Connective s1 And s2) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
    in
      (Connective s1' And s2')
distributeAndOverOr (Connective s1 Or s2) =
    let
      s1' = distributeAndOverOr s1
      s2' = distributeAndOverOr s2
    in
      (Connective s1' Or s2')
distributeAndOverOr s@(Connective _ _ _) = s
distributeAndOverOr s@(Predicate _ _) = s
distributeAndOverOr s@(Equal _ _) = s
distributeAndOverOr (Not s) =
    Not (distributeAndOverOr s)
distributeAndOverOr (Quantifier q vs s) =
    Quantifier q vs (distributeAndOverOr s)
--distributeAndOverOr s = s
-}

{-
 - Skolemization is tge process of removing existential quantifiers by
 - elimination.
-}
skolemize :: (Eq v, Skolem f) => Sentence v p f -> Sentence v p f
skolemize s = skolemize' 1 s [] []

skolemize' :: (Eq v, Skolem f) => Int -> Sentence v p f -> [v] -> [(v, Term v f)] -> Sentence v p f
skolemize' i (Quantifier ForAll vs s) univ skmap =
    skolemize' i s (univ ++ vs) skmap
skolemize' i (Quantifier ExistsCh vs s) univ skmap =
    skolemize' (i + length vs) s univ (skmap ++ (skolemCh i vs univ))
skolemize' i (Connective s1 c s2) univ skmap =
    Connective (skolemize' i s1 univ skmap) c (skolemize' i s2 univ skmap)
skolemize' i (Not s) univ skmap =
    Not (skolemize' i s univ skmap)
skolemize' _i (Equal t1 t2) _univ skmap =
    Equal (substituteCh t1 skmap) (substituteCh t2 skmap)
skolemize' _i (Predicate p terms) _univ skmap =
    Predicate p (map (\x -> substituteCh x skmap) terms)

skolemCh :: Skolem f => Int -> [v] -> [v] -> [(v, Term v f)]
skolemCh _i [] _u = []
skolemCh i (v:vs) u = let
                      skolems =  skolemCh (i + 1) vs u
		    in
		      if null u then
		        (v, Function (toSkolem i) []):skolems
		      else
		        (v, Function (toSkolem i) (map Variable u)):skolems

substituteCh :: (Eq v) => Term v f -> [(v, Term v f)] -> Term v f
substituteCh (Variable v) [] = Variable v
substituteCh var@(Variable v) ((v', t):xs) =
    if v == v' then
      t
    else
      substituteCh var xs
substituteCh (Function f terms) xs =
    Function f (map (\x -> substituteCh x xs) terms)


{--
 - Convert disjunctions to implication:
 -   Collect the negative literals and put them on the left hand side, and
 -   positive literals and put them on the right hand side of the implication.
 -
 - Invariants: The input Sentence is in CNF
 --}

disjunctionToImplication :: Boolean p => Sentence v p f -> Sentence v p f
disjunctionToImplication s =
    let
      cnfL = collectCnf s
      cnfL' = map disjunctionToImplication' cnfL
    in
      foldl (\s1 -> \s2 -> Connective s1 And s2) (head cnfL') (tail cnfL')

disjunctionToImplication' :: Boolean p => Sentence v p f -> Sentence v p f
disjunctionToImplication' s =
    let
      norm = normalize s
      neg' = filter (\ns -> case ns of
		              (NFNot _) -> True
		              _ -> False) norm
      neg = map (\ns -> case ns of
		          (NFNot x) -> x
		          _ -> error "negative literal on LHS") neg'
      pos = filter (\ns -> case ns of
			     (NFNot _) -> False
		             _ -> True) norm
    in
      Connective (denormalize And neg) Imply (denormalize Or pos)

collectCnf :: Sentence v p f -> [Sentence v p f]
collectCnf (Connective s1 And s2) = collectCnf s1 ++ collectCnf s2
collectCnf s = [s]

denormalize :: Boolean p => Connective -> [NormalSentence v p f] -> Sentence v p f
denormalize Imply _ = error "denormalizing =>"
denormalize Equiv _ = error "denormalizing <=>"
denormalize And [] = Predicate (fromBool True) []
denormalize Or [] = Predicate (fromBool False) []
denormalize _c (x:[]) = denormalize' x
denormalize c (x:xs) = Connective (denormalize' x) c (denormalize c xs)

denormalize' :: NormalSentence v p f -> Sentence v p f
denormalize' (NFNot s) = denormalize' s
denormalize' (NFPredicate p ts) = Predicate p ts
denormalize' (NFEqual t1 t2) = Equal t1 t2

normalize :: Sentence v p f -> [NormalSentence v p f]
normalize (Connective s1 And s2) = (normalize s1) ++ (normalize s2)
normalize (Connective s1 Or s2) = (normalize s1) ++ (normalize s2)
normalize (Connective _s1 _ _s2) = error "normailizing unexpected connective"
normalize (Quantifier _ _ _) = error "normalizing quantifier"
normalize (Not s) = [NFNot ((head . normalize) s)]
normalize (Predicate p ts) = [NFPredicate p ts]
normalize (Equal t1 t2) = [NFEqual t1 t2]
