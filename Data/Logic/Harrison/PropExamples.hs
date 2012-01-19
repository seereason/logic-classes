{-# LANGUAGE FlexibleContexts, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeSynonymInstances #-}
module Data.Logic.Harrison.PropExamples where

import Data.Bits (Bits, shiftR)
import Data.Logic.Classes.Combine ((.<=>.), (.=>.), (.&.), (.|.), Combinable, Combination(..), BinOp(..))
import Data.Logic.Classes.Constants (true, false)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Propositional (PropositionalFormula(..))
import Data.Logic.Harrison.Lib (allsets)
import Data.Logic.Harrison.Prop
import Data.Logic.Types.Propositional (Formula(..))
import Test.HUnit
import qualified Data.Set as Set
import Prelude hiding (sum)

-- ========================================================================= 
-- Some propositional formulas to test, and functions to generate classes.   
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

-- ------------------------------------------------------------------------- 
-- Generate assertion equivalent to R(s,t) <= n for the Ramsey number R(s,t) 
-- ------------------------------------------------------------------------- 

data Atom a = P String a (Maybe a) deriving (Eq, Ord, Show)

ramsey :: forall a a1 a2 formula.
          (PropositionalFormula formula (Atom a2),
           Ord formula, Ord a2, Num a, Num a1, Num a2, Enum a2) =>
          a1 -> a -> a2 -> formula
ramsey s t n =
  let vertices = Set.fromList [1 .. n] in
  let yesgrps = Set.map (allsets (2 :: Int)) (allsets s vertices)
      nogrps = Set.map (allsets (2 :: Int)) (allsets t vertices) in
  let e xs = let [m, n] = Set.toAscList xs in atomic (P "p" m (Just n)) in
  list_disj (Set.map (list_conj . Set.map e) yesgrps) .|. list_disj (Set.map (list_conj . Set.map (\ p -> (.~.)(e p))) nogrps)

-- ------------------------------------------------------------------------- 
-- Some currently tractable examples.                                        
-- ------------------------------------------------------------------------- 

{-
START_INTERACTIVE;;
ramsey 3 3 4;;

tautology(ramsey 3 3 5);;

tautology(ramsey 3 3 6);;

END_INTERACTIVE;;
-}

-- ------------------------------------------------------------------------- 
-- Half adder.                                                               
-- ------------------------------------------------------------------------- 

halfsum :: forall formula. Combinable formula => formula -> formula -> formula
halfsum x y = x .<=>. ((.~.) y)

halfcarry :: forall formula. Combinable formula => formula -> formula -> formula
halfcarry x y = x .&. y

ha :: forall formula. Combinable formula => formula -> formula -> formula -> formula -> formula
ha x y s c = (s .<=>. halfsum x y) .&. (c .<=>. halfcarry x y)

-- ------------------------------------------------------------------------- 
-- Full adder.                                                               
-- ------------------------------------------------------------------------- 

carry :: forall formula. Combinable formula => formula -> formula -> formula -> formula
carry x y z = (x .&. y) .|. ((x .|. y) .&. z)

sum :: forall formula. Combinable formula => formula -> formula -> formula -> formula
sum x y z = halfsum (halfsum x y) z

fa :: forall formula. Combinable formula => formula -> formula -> formula -> formula -> formula -> formula
fa x y z s c = (s .<=>. sum x y z) .&. (c .<=>. carry x y z)

-- ------------------------------------------------------------------------- 
-- Useful idiom.                                                             
-- ------------------------------------------------------------------------- 

conjoin :: forall formula atomic a. (PropositionalFormula formula atomic, Ord formula, Ord a) => (a -> formula) -> Set.Set a -> formula
conjoin f l = list_conj (Set.map f l)

-- ------------------------------------------------------------------------- 
-- n-bit ripple carry adder with carry c(0) propagated in and c(n) out.      
-- ------------------------------------------------------------------------- 

ripplecarry :: forall formula atomic a. (PropositionalFormula formula atomic, Ord a, Ord formula, Num a, Enum a) =>
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

mk_index :: forall formula a. PropositionalFormula formula (Atom a) => String -> a -> formula
mk_index x i = atomic (P x i Nothing)
mk_index2 :: forall formula a. PropositionalFormula formula (Atom a) => String -> a -> a -> formula
mk_index2 x i j = atomic (P x i (Just j))

{-
START_INTERACTIVE;;

let [x; y; out; c] = map mk_index ["X"; "Y"; "OUT"; "C"];;

ripplecarry x y c out 2;;

END_INTERACTIVE;;
-}

-- ------------------------------------------------------------------------- 
-- Special case with 0 instead of c(0).                                      
-- ------------------------------------------------------------------------- 

ripplecarry0 :: forall formula atomic a. (PropositionalFormula formula atomic, Ord formula, Ord a, Num a, Enum a) =>
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

ripplecarry1 :: forall formula atomic a. (PropositionalFormula formula atomic, Ord formula, Ord a, Num a, Enum a) =>
                (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> (a -> formula)
             -> a -> formula
ripplecarry1 x y c out n =
  psimplify
   (ripplecarry x y (\ i -> if i == 0 then true else c i) out n)

mux :: forall formula. Combinable formula => formula -> formula -> formula -> formula
mux sel in0 in1 = (((.~.) sel) .&. in0) .|. (sel .&. in1)

offset :: forall t a. Num a => a -> (a -> t) -> a -> t
offset n x i = x (n + i)

carryselect :: forall formula atomic a. (PropositionalFormula formula atomic, Ord a, Ord formula, Num a, Enum a) =>
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

mk_adder_test :: forall formula a. (PropositionalFormula formula (Atom a), Ord a, Ord formula, Num a, Enum a) =>
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

rippleshift :: forall formula atomic a. (PropositionalFormula formula atomic, Ord a, Ord formula, Num a, Enum a) =>
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

multiplier :: forall formula atomic a. (PropositionalFormula formula atomic, Ord a, Ord formula, Num a, Enum a) =>
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

bitlength :: forall b a. (Bits b, Num a) => b -> a
bitlength x = if x == 0 then 0 else 1 + bitlength (shiftR x 1);;

bit :: forall a b. (Bits b, Num a, Integral b) => a -> b -> Bool
bit n x = if n == 0 then x `mod` 2 == 1 else bit (n - 1) (shiftR x 1)

congruent_to :: forall formula atomic a b. (Bits b, PropositionalFormula formula atomic, Ord a, Ord formula, Num a, Integral b, Enum a) =>
                (a -> formula) -> b -> a -> formula
congruent_to x m n =
  conjoin (\ i -> if bit i m then x i else (.~.)(x i))
          (Set.fromList [0 .. (n - 1)])

prime :: forall formula. (PropositionalFormula formula (Atom Int), Ord formula) =>
         Integer -> formula
prime p =
  let [x, y, out] = map mk_index ["x", "y", "out"] in
  let m i j = (x i) .&. (y j)
      [u, v] = map mk_index2 ["u", "v"] in
  let (n :: Int) = bitlength p in
  (.~.) (multiplier m u v out (n - 1) .&. congruent_to out p (max n (2 * n - 2)))

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 

type F = Formula (Atom Int)

deriving instance Show F

{-
instance Constants F where
    fromBool True = 
-}

tests :: Test
tests =
    TestList [TestCase (assertEqual "tautology(prime 7)" True (tautology(prime 7 :: F))),
              TestCase (assertEqual "tautology(prime 9)" False (tautology(prime 9 :: F))),
              TestCase (assertEqual "tautology(prime 11)" True (tautology(prime 11 :: F)))]
