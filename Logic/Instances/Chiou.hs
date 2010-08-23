{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-orphans -fno-warn-missing-signatures #-}
module Logic.Instances.Chiou
    ( Sentence(..)
    , CTerm(..)
    , Connective(..)
    , Quantifier(..)
    , ConjunctiveNormalForm(..)
    , ImplicativeNormalForm(..)
    , NormalSentence(..)
    , NormalTerm(..)
    , toSentence
    , fromSentence
    ) where

import Data.Generics (Data, Typeable)
import qualified Data.Set as S
import Data.String (IsString(..))
import Logic.FirstOrder (FirstOrderLogic(..), Pretty, Term(..))
import qualified Logic.FirstOrder as Logic
import Logic.Implicative (Implicative(..))
import Logic.Logic (Logic(..), BinOp(..), Combine(..), Boolean(..))
import Logic.Propositional (PropositionalLogic(..))
import Logic.FirstOrder (Skolem(..), Quant(..))


-- |This enum instance is used to generate a series of new variable
-- names.
{-
instance Enum String where
    succ v =
        toEnum (if n < cnt then n + 1 else if n == cnt then ord pref + cnt else n + cnt)
            where n = fromEnum v
    fromEnum s =
        case break (not . isDigit) (reverse s) of
          ("", [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn
          (n, [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn + cnt * (read (reverse n) :: Int)
          _ -> error $ "Invalid variable name: " ++ show s
    toEnum n =
        chr (ord mn + pre) : if suf == 0 then "" else show suf
        where (suf, pre) = divMod n cnt

mn = 'x'
pref = 'x'
mx = 'z'
cnt = ord mx - ord mn + 1
-}

data Sentence v p f
    = Connective (Sentence v p f) Connective (Sentence v p f)
    | Quantifier Quantifier [v] (Sentence v p f)
    | Not (Sentence v p f)
    | Predicate p [CTerm v f]
    | Equal (CTerm v f) (CTerm v f)
    deriving (Eq, Ord, Data, Typeable, Show)

data CTerm v f
    = Function f [CTerm v f]
    | Variable v
    deriving (Eq, Ord, Data, Typeable, Show)

data Connective
    = Imply
    | Equiv
    | And
    | Or
    deriving (Eq, Ord, Show, Data, Typeable)

data Quantifier
    = ForAll
    | ExistsCh
    deriving (Eq, Ord, Show, Data, Typeable)

instance Logic (Sentence v p f) where
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y
    (.~.) x   = Not x

instance (Ord v, IsString v, Data v, Pretty v, Show v, Enum v, 
          Ord p, IsString p, Data p, Pretty p, Show p, Boolean p, Logic.Predicate p,
          Ord f, IsString f, Data f, Pretty f, Show f, Skolem f, 
          Logic (Sentence v p f)) =>
         PropositionalLogic (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Predicate p ts) = pApp p ts
    atomic (Equal t1 t2) = t1 .=. t2
    foldF0 c a formula =
        case formula of
          Not x -> c ((:~:) x)
          Quantifier _ _ _ -> error "Logic.Instance.Chiou.foldF0: unexpected"
          Connective f1 Imply f2 -> c (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> c (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> c (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> c (BinOp f1 (:|:) f2)
          Predicate p ts -> a (Predicate p ts)
          Equal t1 t2 -> a (Equal t1 t2)

data AtomicFunction
    = AtomicFunction String
    -- This is redundant with the SkolemFunction and SkolemConstant
    -- constructors in the Chiou Term type.
    | AtomicSkolemFunction Int
    deriving (Eq, Show)

instance IsString AtomicFunction where
    fromString = AtomicFunction

instance Skolem AtomicFunction where
    toSkolem = AtomicSkolemFunction 
    fromSkolem (AtomicSkolemFunction n) = Just n
    fromSkolem _ = Nothing

instance (Pretty v, Pretty p, Pretty f, Show v, Show p, Show f, -- debugging
          Ord v, IsString v, Enum v, Data v,
          Ord p, IsString p, Boolean p, Data p, Logic.Predicate p,
          Ord f, IsString f, Skolem f, Data f, 
          PropositionalLogic (Sentence v p f) (Sentence v p f)) =>
          FirstOrderLogic (Sentence v p f) (CTerm v f) v p f where
    for_all v x = Quantifier ForAll [v] x
    exists v x = Quantifier ExistsCh [v] x
    foldF q c p f =
        case f of
          Not x -> c ((:~:) x)
          Quantifier op (v:vs) f' ->
              let op' = case op of
                          ForAll -> Logic.All
                          ExistsCh -> Logic.Exists in
              -- Use Logic.quant' here instead of the constructor
              -- Quantifier so as not to create quantifications with
              -- empty variable lists.
              q op' v (Logic.quant' op' vs f')
          Quantifier _ [] f' -> foldF q c p f'
          Connective f1 Imply f2 -> c (BinOp f1 (:=>:) f2)
          Connective f1 Equiv f2 -> c (BinOp f1 (:<=>:) f2)
          Connective f1 And f2 -> c (BinOp f1 (:&:) f2)
          Connective f1 Or f2 -> c (BinOp f1 (:|:) f2)
          Predicate name ts -> p name ts
          Equal t1 t2 -> p Logic.eq [t1, t2]
    zipF q c p f1 f2 =
        case (f1, f2) of
          (Not f1', Not f2') -> c ((:~:) f1') ((:~:) f2')
          (Quantifier op1 (v1:vs1) f1', Quantifier op2 (v2:vs2) f2') ->
              if op1 == op2
              then let op' = case op1 of
                               ForAll -> Logic.All
                               ExistsCh -> Logic.Exists in
                   q op' v1 (Quantifier op1 vs1 f1') All v2 (Quantifier op2 vs2 f2')
              else Nothing
          (Quantifier q1 [] f1', Quantifier q2 [] f2') ->
              if q1 == q2 then zipF q c p f1' f2' else Nothing
          (Connective l1 op1 r1, Connective l2 op2 r2) ->
              case (op1, op2) of
                (And, And) -> c (BinOp l1 (:&:) r1) (BinOp l2 (:&:) r2)
                (Or, Or) -> c (BinOp l1 (:|:) r1) (BinOp l2 (:|:) r2)
                (Imply, Imply) -> c (BinOp l1 (:=>:) r1) (BinOp l2 (:=>:) r2)
                (Equiv, Equiv) -> c (BinOp l1 (:<=>:) r1) (BinOp l2 (:<=>:) r2)
                _ -> Nothing
          (Equal l1 r1, Equal l2 r2) -> p Logic.eq [l1,r1] Logic.eq [l2,r2]
          (Predicate p1 ts1, Predicate p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp x [a, b] | x == Logic.eq = Equal a b
    pApp x args = Predicate x args
    -- fApp (AtomicSkolemFunction n) [] = SkolemConstant n
    -- fApp (AtomicSkolemFunction n) ts = SkolemFunction n ts
    x .=. y = Equal x y
    x .!=. y = Not (Equal x y)

{-
instance (FirstOrderLogic (Sentence v p f) (CTerm v f) v p f, Show v, Show p, Show f) => Show (Sentence v p f) where
    show = showForm

instance (FirstOrderLogic (Sentence v p f) (CTerm v f) v p f, Show v, Show p, Show f) => Show (CTerm v f) where
    show = showTerm
-}

instance (Ord v, Enum v, Data v, Eq f, Skolem f, Data f) => Logic.Term (CTerm v f) v f where
    foldT v fn t =
        case t of
          Variable x -> v x
          Function f ts -> fn f ts
    zipT  v f t1 t2 =
        case (t1, t2) of
          (Variable v1, Variable v2) -> v v1 v2
          (Function f1 ts1, Function f2 ts2) -> f f1 ts1 f2 ts2
          _ -> Nothing
    var = Variable
    fApp f ts = Function f ts

data ConjunctiveNormalForm v p f =
    CNF [Sentence v p f]
    deriving (Eq)

data ImplicativeNormalForm v p f
    = INF [Sentence v p f] [Sentence v p f]
    deriving (Eq, Data, Show, Typeable)

data NormalSentence v p f
    = NFNot (NormalSentence v p f)
    | NFPredicate p [NormalTerm v f]
    | NFEqual (NormalTerm v f) (NormalTerm v f)
    deriving (Eq, Ord, Show, Data, Typeable)

-- We need a distinct type here because of the functional dependencies
-- in class FirstOrderLogic.
data NormalTerm v f
    = NormalFunction f [NormalTerm v f]
    | NormalVariable v
    deriving (Eq, Ord, Show, Data, Typeable)

instance (Enum v, Ord p, Show p, Ord f, Show f,
          FirstOrderLogic (Sentence v p f) (CTerm v f) v p f) => Implicative (ImplicativeNormalForm v p f) (Sentence v p f) where
    neg (INF x _) = S.fromList x
    pos (INF _ x) = S.fromList x
    makeINF lhs rhs = INF (S.toList lhs) (S.toList rhs)

instance Logic (NormalSentence v p f) where
    (.~.) x   = NFNot x
    _ .|. _ = error "NormalSentence |"

instance (IsString v, Pretty v, Show v,
          Ord p, IsString p, Boolean p, Data p, Pretty p, Show p, Logic.Predicate p,
          Ord f, IsString f, Pretty f, Show f,
          Logic (NormalSentence v p f), Logic.Term (NormalTerm v f) v f) => FirstOrderLogic (NormalSentence v p f) (NormalTerm v f) v p f where
    for_all _ _ = error "FirstOrderLogic NormalSentence"
    exists _ _ = error "FirstOrderLogic NormalSentence"
    foldF _ c p f =
        case f of
          NFNot x -> c ((:~:) x)
          NFEqual t1 t2 -> p Logic.eq [t1, t2]
          NFPredicate pr ts -> p pr ts
    zipF _ c p f1 f2 =
        case (f1, f2) of
          (NFNot f1', NFNot f2') -> c ((:~:) f1') ((:~:) f2')
          (NFEqual f1l f1r, NFEqual f2l f2r) -> p Logic.eq [f1l, f1r] Logic.eq [f2l, f2r]
          (NFPredicate p1 ts1, NFPredicate p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp p args = NFPredicate p args
    x .=. y = NFEqual x y
    x .!=. y = NFNot (NFEqual x y)

instance (Ord v, Enum v, Data v, Eq f, Logic.Skolem f, Data f) => Logic.Term (NormalTerm v f) v f where
    var = NormalVariable
    fApp = NormalFunction
    foldT v f t =
            case t of
              NormalVariable x -> v x
              NormalFunction x ts -> f x ts
    zipT v fn t1 t2 =
        case (t1, t2) of
          (NormalVariable x1, NormalVariable x2) -> v x1 x2
          (NormalFunction f1 ts1, NormalFunction f2 ts2) -> fn f1 ts1 f2 ts2
          _ -> Nothing

toSentence :: FirstOrderLogic (Sentence v p f) (CTerm v f) v p f => NormalSentence v p f -> Sentence v p f
toSentence (NFNot s) = (.~.) (toSentence s)
toSentence (NFEqual t1 t2) = toTerm t1 .=. toTerm t2
toSentence (NFPredicate p ts) = pApp p (map toTerm ts)

toTerm :: (Ord v, Enum v, Data v, Eq f, Logic.Skolem f, Data f) => NormalTerm v f -> CTerm v f
toTerm (NormalFunction f ts) = Logic.fApp f (map toTerm ts)
toTerm (NormalVariable v) = Logic.var v

fromSentence :: forall v p f. FirstOrderLogic (Sentence v p f) (CTerm v f) v p f =>
                Sentence v p f -> NormalSentence v p f
fromSentence = foldF 
                 (\ _ _ _ -> error "fromSentence 1")
                 (\ cm ->
                      case cm of
                        ((:~:) f) -> NFNot (fromSentence f)
                        _ -> error "fromSentence 2")
                 (\ p ts ->
                      case ts of
                        [t1,t2] | p == Logic.eq -> NFEqual (fromTerm t1) (fromTerm t2)
                        _ | p == Logic.eq -> error ("Arity error for " ++ show p)
                        _ -> NFPredicate p (map fromTerm ts))


fromTerm :: CTerm v f -> NormalTerm v f
fromTerm (Function f ts) = NormalFunction f (map fromTerm ts)
fromTerm (Variable v) = NormalVariable v
