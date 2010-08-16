{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             RankNTypes, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-orphans -fno-warn-missing-signatures #-}
module Logic.Instances.Chiou () where

import Data.Char (ord, isDigit, chr)
import Data.Generics (Data)
import Data.String (IsString(..))
import Logic.Chiou.FirstOrderLogic
import Logic.Logic (Logic(..), BinOp(..), Boolean(..))
import Logic.Propositional (PropositionalLogic(..))
import Logic.FirstOrder (Skolem(..), FirstOrderLogic(..), InfixPred(..), Quant(..), Pretty, showForm, showTerm)
import qualified Logic.FirstOrder as Logic

-- |This enum instance is used to generate a series of new variable
-- names.
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

instance Logic (Sentence v p f) where
    x .<=>. y = Connective x Equiv y
    x .=>.  y = Connective x Imply y
    x .|.   y = Connective x Or y
    x .&.   y = Connective x And y
    (.~.) x   = Not x

instance (Logic (Sentence v p f), Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f) =>
         PropositionalLogic (Sentence v p f) (Sentence v p f) where
    atomic (Connective _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Quantifier _ _ _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Not _) = error "Logic.Instances.Chiou.atomic: unexpected"
    atomic (Predicate p ts) = pApp p ts
    atomic (Equal t1 t2) = t1 .=. t2
    foldF0 n b a formula =
        case formula of
          Not x -> n x
          Quantifier _ _ _ -> error "Logic.Instance.Chiou.foldF0: unexpected"
          Connective f1 Imply f2 -> b f1 (:=>:) f2
          Connective f1 Equiv f2 -> b f1 (:<=>:) f2
          Connective f1 And f2 -> b f1 (:&:) f2
          Connective f1 Or f2 -> b f1 (:|:) f2
          Predicate p ts -> a (Predicate p ts)
          Equal t1 t2 -> a (Equal t1 t2)

-- |We need a type to represent the atomic function, which is any term
-- which is not a variable.
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

instance (PropositionalLogic (Sentence v p f) (Sentence v p f), Ord v, Enum v, Data v, Ord p, Boolean p, Data p, Ord f, Skolem f, Data f, Pretty v, Pretty p, Pretty f) =>
          FirstOrderLogic (Sentence v p f) (CTerm v f) v p f where
    for_all vars x = Quantifier ForAll vars x
    exists vars x = Quantifier ExistsCh vars x
    foldF n q b i p f =
        case f of
          Not x -> n x
          Quantifier ForAll vs f' -> q Logic.All vs f'
          Quantifier ExistsCh vs f' -> q Logic.Exists vs f'
          Connective f1 Imply f2 -> b f1 (:=>:) f2
          Connective f1 Equiv f2 -> b f1 (:<=>:) f2
          Connective f1 And f2 -> b f1 (:&:) f2
          Connective f1 Or f2 -> b f1 (:|:) f2
          Predicate name ts -> p name ts
          Equal t1 t2 -> i t1 (:=:) t2
    zipF n q b i p f1 f2 =
        case (f1, f2) of
          (Not f1', Not f2') -> n f1' f2'
          (Quantifier q1 vs1 f1', Quantifier q2 vs2 f2') ->
              case (q1, q2) of
                (ForAll, ForAll) -> q All vs1 f1' All vs2 f2'
                (ExistsCh, ExistsCh) -> q Exists vs1 f1' Exists vs2 f2'
                _ -> Nothing
          (Connective l1 op1 r1, Connective l2 op2 r2) ->
              case (op1, op2) of
                (And, And) -> b l1 (:&:) r1 l2 (:&:) r2
                (Or, Or) -> b l1 (:|:) r1 l2 (:|:) r2
                (Imply, Imply) -> b l1 (:=>:) r1 l2 (:=>:) r2
                (Equiv, Equiv) -> b l1 (:<=>:) r1 l2 (:<=>:) r2
                _ -> Nothing
          (Equal l1 r1, Equal l2 r2) -> i l1 (:=:) r1 l2 (:=:) r2
          (Predicate p1 ts1, Predicate p2 ts2) -> p p1 ts1 p2 ts2
          _ -> Nothing
    pApp x args = Predicate x args
    -- fApp (AtomicSkolemFunction n) [] = SkolemConstant n
    -- fApp (AtomicSkolemFunction n) ts = SkolemFunction n ts
    x .=. y = Equal x y
    x .!=. y = Not (Equal x y)

instance (FirstOrderLogic (Sentence v p f) (CTerm v f) v p f, Show v, Show p, Show f) => Show (Sentence v p f) where
    show = showForm

instance (FirstOrderLogic (Sentence v p f) (CTerm v f) v p f, Show v, Show p, Show f) => Show (CTerm v f) where
    show = showTerm

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

{-
cnf2 :: FirstOrderLogic formula term v p f =>
        (v -> Variable) -> (p -> Predicate) -> (f -> AtomicFunction) -> formula -> formula
cnf2 cv cp cf f = f''
    where
      -- Convert from Sentence
      f'' :: FirstOrderLogic formula term v p f => formula
      f'' = convertFOF cv' cp' cf' f'
      -- Convert to Sentence
      f' :: Sentence
      f' = toCNFSentence (convertFOF cv cp cf f)
-}
{-
      cv' = undefined -- fromString
      cp' = undefined -- fromString
      -- cf' :: String -> AtomicFunction
      cf' = undefined -- (AtomicFunction s) = s
-}
