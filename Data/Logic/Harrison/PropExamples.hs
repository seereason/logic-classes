{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
module Data.Logic.Harrison.PropExamples
    ( Atom(..)
    , N
    , prime
    , ramsey
    , tests
    ) where

import Data.Bits (Bits, shiftR)
import Data.Logic.Classes.Combine ((.<=>.), (.=>.), (.&.), (.|.), IsCombinable{-, Combination(..), BinOp(..)-})
import Data.Logic.Classes.Constants (true, false)
import qualified Data.Logic.Classes.Formula as C
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Pretty (Pretty(pPrint), HasFixity(..), leafFixity)
import Data.Logic.Classes.Propositional (IsPropositional(..))
import Data.Logic.Harrison.Lib (allsets)
import Data.Logic.Harrison.Prop (tautology, list_conj, list_disj, psimplify)
import Data.Logic.Types.Propositional (Formula(..))
import qualified Data.Set as Set
import Prelude hiding (sum)
import Test.HUnit
import Text.PrettyPrint (text)

tests :: Test
tests = TestList [test01, {-test02,-} test03]

-- ========================================================================= 
-- Some propositional formulas to test, and functions to generate classes.   
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t) 
-- ------------------------------------------------------------------------- 

data Atom a = P String a (Maybe a) deriving (Eq, Ord, Show)

instance Pretty (Atom N) where
    pPrint (P s n mm) = text (s ++ show n ++ maybe "" (\ m -> "." ++ show m) mm)

instance HasFixity (Atom N) where
    fixity = const leafFixity

type N = Integer

type F = Formula (Atom N)

-- deriving instance Show F

ramsey :: forall formula.
          (IsPropositional formula (Atom N), Ord formula) =>
          Int -> Int -> N -> formula
ramsey s t n =
  let vertices = Set.fromList [1 .. n] in
  let yesgrps = Set.map (allsets (2 :: Int)) (allsets s vertices)
      nogrps = Set.map (allsets (2 :: Int)) (allsets t vertices) in
  let e xs = let [m, n] = Set.toAscList xs in C.atomic (P "p" m (Just n)) in
  list_disj (Set.map (list_conj . Set.map e) yesgrps) .|. list_disj (Set.map (list_conj . Set.map (\ p -> (.~.)(e p))) nogrps)

-- ------------------------------------------------------------------------- 
-- Some currently tractable examples.                                        
-- ------------------------------------------------------------------------- 

test01 :: Test
test01 = TestList [{- TestCase (assertEqual "ramsey 3 3 4"
                                             (Combine
                                              (BinOp
                                               (Combine
                                                (BinOp
                                                 (Combine
                                                  (BinOp
                                                   (Atom (P "p" 1 (Just 4)))
                                                   (:&:)
                                                   (Combine
                                                    (BinOp
                                                     (Atom (P "p" 2 (Just 4)))
                                                     (:&:)
                                                     (Atom (P "p" 1 (Just 2)))))))
                                                 (:|:)
                                                 (Combine
                                                  (BinOp
                                                   (Combine
                                                    (BinOp
                                                     (Atom (P "p" 1 (Just 4)))
                                                     (:&:)
                                                     (Combine
                                                      (BinOp
                                                       (Atom (P "p" 3 (Just 4)))
                                                       (:&:)
                                                       (Atom (P "p" 1 (Just 3)))))))
                                                   (:|:)
                                                   (Combine
                                                    (BinOp
                                                     (Combine
                                                      (BinOp
                                                       (Atom (P "p" 2 (Just 4)))
                                                       (:&:)
                                                       (Combine
                                                        (BinOp
                                                         (Atom (P "p" 3 (Just 4)))
                                                         (:&:)
                                                         (Atom (P "p" 2 (Just 3)))))))
                                                     (:|:)
                                                     (Combine
                                                      (BinOp
                                                       (Atom (P "p" 1 (Just 3)))
                                                       (:&:)
                                                       (Combine
                                                        (BinOp
                                                         (Atom (P "p" 2 (Just 3)))
                                                         (:&:)
                                                         (Atom (P "p" 1 (Just 2)))))))))))))
                                               (:|:)
                                               (Combine
                                                (BinOp
                                                 (Combine
                                                  (BinOp (Combine
                                                          ((:~:) (Atom (P "p" 1 (Just 4))))) (:&:)
                                                   (Combine
                                                    (BinOp
                                                     (Combine
                                                      ((:~:) (Atom (P "p" 2 (Just 4)))))
                                                     (:&:)
                                                     (Combine
                                                      ((:~:) (Atom (P "p" 1 (Just 2)))))))))
                                                 (:|:)
                                                 (Combine
                                                  (BinOp
                                                   (Combine
                                                    (BinOp (Combine
                                                            ((:~:) (Atom (P "p" 1 (Just 4)))))
                                                     (:&:)
                                                     (Combine
                                                      (BinOp
                                                       (Combine
                                                        ((:~:) (Atom (P "p" 3 (Just 4)))))
                                                       (:&:)
                                                       (Combine
                                                        ((:~:) (Atom (P "p" 1 (Just 3)))))))))
                                                   (:|:)
                                                   (Combine
                                                    (BinOp
                                                     (Combine
                                                      (BinOp
                                                       (Combine
                                                        ((:~:) (Atom (P "p" 2 (Just 4)))))
                                                       (:&:)
                                                       (Combine
                                                        (BinOp
                                                         (Combine
                                                          ((:~:) (Atom (P "p" 3 (Just 4)))))
                                                         (:&:)
                                                         (Combine
                                                          ((:~:) (Atom (P "p" 2 (Just 3)))))))))
                                                     (:|:)
                                                     (Combine
                                                      (BinOp
                                                       (Combine
                                                        ((:~:) (Atom (P "p" 1 (Just 3)))))
                                                       (:&:)
                                                       (Combine
                                                        (BinOp
                                                         (Combine
                                                          ((:~:) (Atom (P "p" 2 (Just 3)))))
                                                         (:&:)
                                                         (Combine
                                                          ((:~:) (Atom (P "p" 1 (Just 2)))))))))))))))))
                                         (ramsey 3 3 4 :: Formula (Atom N))), -}
                   TestCase (assertEqual "tautology (ramsey 3 3 5)" False (tautology (ramsey 3 3 5 :: Formula (Atom N)))),
                   TestCase (assertEqual "tautology (ramsey 3 3 6)" True (tautology (ramsey 3 3 6 :: Formula (Atom N))))]

-- ------------------------------------------------------------------------- 
-- Half adder.                                                               
-- ------------------------------------------------------------------------- 

halfsum :: forall formula. IsCombinable formula => formula -> formula -> formula
halfsum x y = x .<=>. ((.~.) y)

halfcarry :: forall formula. IsCombinable formula => formula -> formula -> formula
halfcarry x y = x .&. y

ha :: forall formula. IsCombinable formula => formula -> formula -> formula -> formula -> formula
ha x y s c = (s .<=>. halfsum x y) .&. (c .<=>. halfcarry x y)

-- ------------------------------------------------------------------------- 
-- Full adder.                                                               
-- ------------------------------------------------------------------------- 

carry :: forall formula. IsCombinable formula => formula -> formula -> formula -> formula
carry x y z = (x .&. y) .|. ((x .|. y) .&. z)

sum :: forall formula. IsCombinable formula => formula -> formula -> formula -> formula
sum x y z = halfsum (halfsum x y) z

fa :: forall formula. IsCombinable formula => formula -> formula -> formula -> formula -> formula -> formula
fa x y z s c = (s .<=>. sum x y z) .&. (c .<=>. carry x y z)

-- ------------------------------------------------------------------------- 
-- Useful idiom.                                                             
-- ------------------------------------------------------------------------- 

conjoin :: forall formula atomic a. (IsPropositional formula atomic, Ord formula, Ord a) => (a -> formula) -> Set.Set a -> formula
conjoin f l = list_conj (Set.map f l)

-- ------------------------------------------------------------------------- 
-- n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      
-- ------------------------------------------------------------------------- 

ripplecarry :: forall formula atomic a. (IsPropositional formula atomic, Ord a, Ord formula, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> a -> formula
ripplecarry x y c out n =
    conjoin (\ i -> fa (x i) (y i) (c i) (out i) (c(i + 1))) (Set.fromList [0 .. (n - 1)])

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

mk_index :: forall formula a. IsPropositional formula (Atom a) => String -> a -> formula
mk_index x i = C.atomic (P x i Nothing)
mk_index2 :: forall formula a. IsPropositional formula (Atom a) => String -> a -> a -> formula
mk_index2 x i j = C.atomic (P x i (Just j))

#if 0
test02 = TestCase (assertEqual "ripplecarry x y c out 2"
                               (Combine (BinOp (Combine (BinOp (Combine (BinOp (Atom (P "OUT" 1 Nothing)) (:<=>:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 1 Nothing)) (:<=>:) (Combine ((:~:) (Atom (P "Y" 1 Nothing)))))) (:<=>:) (Combine ((:~:) (Atom (P "C" 1 Nothing)))))))) (:&:)
                                                         (Combine (BinOp (Atom (P "C" 2 Nothing)) (:<=>:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 1 Nothing)) (:&:) (Atom (P "Y" 1 Nothing)))) (:|:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 1 Nothing)) (:|:) (Atom (P "Y" 1 Nothing)))) (:&:) (Atom (P "C" 1 Nothing)))))))))) (:&:)
                                         (Combine (BinOp (Combine (BinOp (Atom (P "OUT" 0 Nothing)) (:<=>:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 0 Nothing)) (:<=>:) (Combine ((:~:) (Atom (P "Y" 0 Nothing)))))) (:<=>:) (Combine ((:~:) (Atom (P "C" 0 Nothing)))))))) (:&:)
                                                   (Combine (BinOp (Atom (P "C" 1 Nothing)) (:<=>:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 0 Nothing)) (:&:) (Atom (P "Y" 0 Nothing)))) (:|:) (Combine (BinOp (Combine (BinOp (Atom (P "X" 0 Nothing)) (:|:) (Atom (P "Y" 0 Nothing)))) (:&:) (Atom (P "C" 0 Nothing))))))))))))
                               {- <<((OUT_0 <=> (X_0 <=> ~Y_0) <=> ~C_0) /\
                                      (C_1 <=> X_0 /\ Y_0 \/ (X_0 \/ Y_0) /\ C_0)) /\
                                     (OUT_1 <=> (X_1 <=> ~Y_1) <=> ~C_1) /\
                                     (C_2 <=> X_1 /\ Y_1 \/ (X_1 \/ Y_1) /\ C_1)>> -}
                               (let [x, y, out, c] = map mk_index ["X", "Y", "OUT", "C"] in
                                ripplecarry x y c out 2 :: Formula (Atom N)))
#endif

-- ------------------------------------------------------------------------- 
-- Special case with 0 instead of c(0).                                      
-- ------------------------------------------------------------------------- 

ripplecarry0 :: forall formula atomic a. (IsPropositional formula atomic, Ord formula, Ord a, Num a, Enum a) =>
                (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> a -> formula
ripplecarry0 x y c out n =
  psimplify
   (ripplecarry x y (\ i -> if i == 0 then false else c i) out n)

-- ------------------------------------------------------------------------- 
-- Carry-select adder                                                        
-- ------------------------------------------------------------------------- 

ripplecarry1 :: forall formula atomic a. (IsPropositional formula atomic, Ord formula, Ord a, Num a, Enum a) =>
                (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> a -> formula
ripplecarry1 x y c out n =
  psimplify
   (ripplecarry x y (\ i -> if i == 0 then true else c i) out n)

mux :: forall formula. IsCombinable formula => formula -> formula -> formula -> formula
mux sel in0 in1 = (((.~.) sel) .&. in0) .|. (sel .&. in1)

offset :: forall t a. Num a => a -> (a -> t) -> a -> t
offset n x i = x (n + i)

carryselect :: forall formula atomic a. (IsPropositional formula atomic, Ord a, Ord formula, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> a -> a -> formula
carryselect x y c0 c1 s0 s1 c s n k =
  let k' = min n k in
  let fm = ((ripplecarry0 x y c0 s0 k') .&. (ripplecarry1 x y c1 s1 k')) .&.
           (((c k') .<=>. (mux (c 0) (c0 k') (c1 k'))) .&.
            (conjoin (\ i -> (s i) .<=>. (mux (c 0) (s0 i) (s1 i)))
                             (Set.fromList [0 .. (k' - 1)]))) in
  if k' < k then fm else
  fm .&. (carryselect
          (offset k x) (offset k y) (offset k c0) (offset k c1)
          (offset k s0) (offset k s1) (offset k c) (offset k s)
          (n - k) k)

-- ------------------------------------------------------------------------- 
-- Equivalence problems for carry-select vs ripple carry adders.             
-- ------------------------------------------------------------------------- 

mk_adder_test :: forall formula a. (IsPropositional formula (Atom a), Ord a, Ord formula, Num a, Enum a) =>
                 a -> a -> formula
mk_adder_test n k =
  let [x, y, c, s, c0, s0, c1, s1, c2, s2] =
          map mk_index ["x", "y", "c", "s", "c0", "s0", "c1", "s1", "c2", "s2"] in
  (((carryselect x y c0 c1 s0 s1 c s n k) .&.
    ((.~.) (c 0))) .&.
   (ripplecarry0 x y c2 s2 n)) .=>.
  (((c n) .<=>. (c2 n)) .&.
   (conjoin (\ i -> (s i) .<=>. (s2 i)) (Set.fromList [0 .. (n - 1)])))

-- ------------------------------------------------------------------------- 
-- Ripple carry stage that separates off the final result.                   
--                                                                           
--       UUUUUUUUUUUUUUUUUUUU  (u)                                           
--    +  VVVVVVVVVVVVVVVVVVVV  (v)                                           
--                                                                           
--    = WWWWWWWWWWWWWWWWWWWW   (w)                                           
--    +                     Z  (z)                                           
-- ------------------------------------------------------------------------- 

rippleshift :: forall formula atomic a. (IsPropositional formula atomic, Ord a, Ord formula, Num a, Enum a) =>
               (a -> formula)
            -> (a -> formula)
            -> (a -> formula)
            -> formula
            -> (a -> formula)
            -> a -> formula
rippleshift u v c z w n =
  ripplecarry0 u v (\ i -> if i == n then w(n - 1) else c(i + 1))
                   (\ i -> if i == 0 then z else w(i - 1)) n
-- ------------------------------------------------------------------------- 
-- Naive multiplier based on repeated ripple carry.                          
-- ------------------------------------------------------------------------- 

multiplier :: forall formula atomic a. (IsPropositional formula atomic, Ord a, Ord formula, Num a, Enum a) =>
              (a -> a -> formula)
           -> (a -> a -> formula)
           -> (a -> a -> formula)
           -> (a -> formula)
           -> a
           -> formula
multiplier x u v out n =
  if n == 1 then ((out 0) .<=>. (x 0 0)) .&. ((.~.)(out 1)) else
  psimplify (((out 0) .<=>. (x 0 0)) .&.
             ((rippleshift
               (\ i -> if i == n - 1 then false else x 0 (i + 1))
               (x 1) (v 2) (out 1) (u 2) n) .&.
              (if n == 2 then ((out 2) .<=>. (u 2 0)) .&. ((out 3) .<=>. (u 2 1)) else
                   conjoin (\ k -> rippleshift (u k) (x k) (v(k + 1)) (out k)
                                   (if k == n - 1 then \ i -> out(n + i)
                                    else u(k + 1)) n) (Set.fromList [2 .. (n - 1)]))))

-- ------------------------------------------------------------------------- 
-- Primality examples.                                                       
-- For large examples, should use "num" instead of "int" in these functions. 
-- ------------------------------------------------------------------------- 

bitlength :: forall b a. (Num a, Num b, Bits b) => b -> a
bitlength x = if x == 0 then 0 else 1 + bitlength (shiftR x 1);;

bit :: forall a b. (Num a, Eq a, Bits b, Integral b) => a -> b -> Bool
bit n x = if n == 0 then x `mod` 2 == 1 else bit (n - 1) (shiftR x 1)

congruent_to :: forall formula atomic a b. (Bits b, IsPropositional formula atomic, Ord a, Ord formula, Num a, Integral b, Enum a) =>
                (a -> formula) -> b -> a -> formula
congruent_to x m n =
  conjoin (\ i -> if bit i m then x i else (.~.)(x i))
          (Set.fromList [0 .. (n - 1)])

prime :: forall formula. (IsPropositional formula (Atom N), Ord formula) => N -> formula
prime p =
  let [x, y, out] = map mk_index ["x", "y", "out"] in
  let m i j = (x i) .&. (y j)
      [u, v] = map mk_index2 ["u", "v"] in
  let (n :: Integer) = bitlength p in
  (.~.) (multiplier m u v out (n - 1) .&. congruent_to out p (max n (2 * n - 2)))

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

test03 :: Test
test03 =
    TestList [TestCase (assertEqual "tautology(prime 7)" True (tautology(prime 7 :: F))),
              TestCase (assertEqual "tautology(prime 9)" False (tautology(prime 9 :: F))),
              TestCase (assertEqual "tautology(prime 11)" True (tautology(prime 11 :: F)))]
