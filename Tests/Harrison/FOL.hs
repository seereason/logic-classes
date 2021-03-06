{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes,
             ScopedTypeVariables, TypeFamilies, TypeSynonymInstances #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Harrison.FOL
    ( tests1
    , tests2
    , example1
    , example2
    , example3
    , example4
    ) where

import Control.Applicative.Error (Failing(..))
import Control.Monad (filterM)
import qualified Data.Map as Map
import qualified Data.Set as Set
import FOL (for_all, exists, Predicate(Equals), MyFormula1,
            HasApplyAndEquate(..), (.=.), IsQuantified(..), IsTerm(vt, fApp, foldTerm), IsVariable(..), pApp, Quant(..))
import Formulas ((.~.), false, IsCombinable(..), BinOp(..))
import Lib ((|->))
import Prelude hiding (pred)
import Skolem (MyFormula, MyTerm, Function)
import Test.HUnit

tests1 :: Test
tests1 = TestLabel "Data.Logic.Tests.Harrison.FOL" $
        TestList [test01, test02, test03, test04, test05,
                  test06, test07, test08, test09]
tests2 :: Test
tests2 = TestLabel "Data.Logic.Tests.Harrison.FOL" $
         TestList [{-test10, test11, test12-}]

-- ------------------------------------------------------------------------- 
-- Semantics, implemented of course for finite domains only.                 
-- ------------------------------------------------------------------------- 

termval :: (IsTerm term v f, Show v) =>
           ([a], f -> [a] -> a, p -> [a] -> Bool)
        -> Map.Map v a
        -> term
        -> Failing a
termval m@(_domain, func, _pred) v tm =
    foldTerm (\ x -> maybe (Failure ["Undefined variable: " ++ show x]) Success (Map.lookup x v))
             (\ f args -> mapM (termval m v) args >>= return . func f)
             tm

holds :: forall formula atom term v p f a.
         (IsQuantified formula atom v, HasApplyAndEquate atom p term, IsTerm term v f, Show v, Eq a) =>
         ([a], f -> [a] -> a, p -> [a] -> Bool)
      -> Map.Map v a
      -> formula
      -> Failing Bool
holds m@(domain, _func, pred) v fm =
    foldQuantified qu co ne tf at fm
    where
      qu op x p = mapM (\ a -> holds m ((|->) x a v) p) domain >>= return . (asPred op) (== True)
      asPred (:?:) = any
      asPred (:!:) = all
      ne p = holds m v p >>= return . not
      co p (:|:) q = (||) <$> (holds m v p) <*> (holds m v q)
      co p (:&:) q = (&&) <$> (holds m v p) <*> (holds m v q)
      co p (:=>:) q = (||) <$> (not <$> (holds m v p)) <*> (holds m v q)
      co p (:<=>:) q = (==) <$> (holds m v p) <*> (holds m v q)
      tf x = Success x
      at :: atom -> Failing Bool
      at = foldEquate (\ t1 t2 -> return $ termval m v t1 == termval m v t2) (\ r args -> mapM (termval m v) args >>= return . pred r)
-- | This becomes a method in FirstOrderFormulaEq, so it is not exported here.
-- (.=.) :: MyTerm -> MyTerm -> Formula FOL
-- a .=. b = Atom (R "=" [a, b])

-- -------------------------------------------------------------------------
-- Example.                                                                 
-- -------------------------------------------------------------------------

{-
instance HasFixity (Formula FOL) where
    fixity = error "FIXME"
-}

example1 :: MyTerm
example1 = fApp "sqrt" [fApp "-" [fApp "1" [], fApp "cos" [fApp "power" [fApp "+" [vt "x", vt "y"], fApp "2" []]]]]
-- example1 = Fn "sqrt" [Fn "-" [Fn "1" [], Fn "cos" [Fn "power" [Fn "+" [vt "x", vt "y"], Fn "2" []]]]]

-- -------------------------------------------------------------------------
-- Trivial example of "x + y < z".                                           
-- ------------------------------------------------------------------------- 

example2 :: MyFormula1
example2 = pApp "<" [fApp "+" [vt "x", vt "y"], vt "z"]
-- example2 = Atom (R "<" [Fn "+" [Var "x", Var "y"], Var "z"])

-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 

example3 :: MyFormula1
example3 = (for_all "x" (pApp "<" [vt "x", fApp "2" []] .=>.
                         pApp "<=" [fApp "*" [fApp "2" [], vt "x"], fApp "3" []])) .|. false
example4 :: MyTerm
example4 = fApp "*" [fApp "2" [], vt "x"]

-- ------------------------------------------------------------------------- 
-- Examples of particular interpretations.                                   
-- ------------------------------------------------------------------------- 

boolInterp :: ([Bool], Function -> [Bool] -> Bool, Predicate -> [Bool] -> Bool)
boolInterp =
    ([False, True],func,pred)
    where
      func f args =
          case (f,args) of
            ("0",[]) -> False
            ("1",[]) -> True
            ("+",[x, y]) -> not (x == y)
            ("*",[x, y]) -> x && y
            _ -> error "uninterpreted function"
      pred p args =
          case (p,args) of
            (Equals, [x, y]) -> x == y
            _ -> error "uninterpreted predicate"

modInterp :: Integer
          -> ([Integer],
              Function -> [Integer] -> Integer,
              Predicate -> [Integer] -> Bool)
modInterp n =
    ([0..(n-1)],func,pred)
    where
      func :: Function -> [Integer] -> Integer
      func f args =
          case (f,args) of
            ("0",[]) -> 0
            ("1",[]) -> 1 `mod` n
            ("+",[x, y]) -> (x + y) `mod` n
            ("*",[x, y]) -> (x * y) `mod` n
            _ -> error "uninterpreted function"
      pred :: Predicate -> [Integer] -> Bool
      pred p args =
          case (p,args) of
            (Equals,[x, y]) -> x == y
            _ -> error "uninterpreted predicate"

test01 :: Test
test01 = TestCase $ assertEqual "holds bool test (p. 126)" expected input
    where input = holds boolInterp Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: MyFormula)
          expected = Success True
test02 :: Test
test02 = TestCase $ assertEqual "holds mod test 1 (p. 126)" expected input
    where input =  holds (modInterp 2) Map.empty (for_all "x" (vt "x" .=. (fApp "0" [] :: MyTerm) .|. vt "x" .=. (fApp "1" [] :: MyTerm)) :: MyFormula)
          expected = Success True
test03 :: Test
test03 = TestCase $ assertEqual "holds mod test 2 (p. 126)" expected input
    where input =  holds (modInterp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .|. vt "x" .=. fApp "1" []) :: MyFormula)
          expected = Success False

test04 :: Test
test04 = TestCase $ assertEqual "holds mod test 3 (p. 126)" expected input
    where input = filterM (\ n -> holds (modInterp n) Map.empty fm) [1..45]
                  where fm = for_all "x" ((.~.) (vt "x" .=. fApp "0" []) .=>. exists "y" (fApp "*" [vt "x", vt "y"] .=. fApp "1" [])) :: MyFormula
          expected = Success [1,2,3,5,7,11,13,17,19,23,29,31,37,41,43]

test05 :: Test
test05 = TestCase $ assertEqual "holds mod test 4 (p. 129)" expected input
    where input = holds (modInterp 3) Map.empty ((for_all "x" (vt "x" .=. fApp "0" [])) .=>. fApp "1" [] .=. fApp "0" [] :: MyFormula)
          expected = Success True
test06 :: Test
test06 = TestCase $ assertEqual "holds mod test 5 (p. 129)" expected input
    where input = holds (modInterp 3) Map.empty (for_all "x" (vt "x" .=. fApp "0" [] .=>. fApp "1" [] .=. fApp "0" []) :: MyFormula)
          expected = Success False

-- ------------------------------------------------------------------------- 
-- Variant function and examples.                                            
-- ------------------------------------------------------------------------- 

test07 :: Test
test07 = TestCase $ assertEqual "variant 1 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["y", "z"]) :: String
          expected = "x"
test08 :: Test
test08 = TestCase $ assertEqual "variant 2 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "y"]) :: String
          expected = "x'"
test09 :: Test
test09 = TestCase $ assertEqual "variant 3 (p. 133)" expected input
    where input = variant "x" (Set.fromList ["x", "x'"]) :: String
          expected = "x''"

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 
{-
-- test10 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test10 =
    let (x, x', y) = (fromString "x", fromString "x'", fromString "y") in
    TestCase $ assertEqual "subst 1 (p. 134)" expected input
    where input = subst (y |=> vt x) (C.for_all x (vt x .=. vt y))
          expected = C.for_all x' (vt x' .=. vt x)

test11 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test11 = TestCase $ assertEqual "subst 2 (p. 134)" expected input
    where input = subst ("y" |=> Var "x") (C.for_all "x" (C.for_all "x'" ((vt "x" .=. vt "y") .=>. (vt "x" .=. vt "x'"))))
          expected = H.Forall "x'" (H.Forall "x''" (Imp (Atom (R "=" [Var "x'",Var "x"])) (Atom (R "=" [Var "x'",Var "x''"]))))

test12 :: forall formula atom term v p f. TestFormulaEq formula atom term v p f => Test formula
test12 = TestCase $ assertEqual "show first order formula 1" expected input
    where input = map show fms
          expected = ["((pApp \"p\" []) .&. (pApp \"q\" [])) .|. (pApp \"r\" [])",
                      "(pApp \"p\" []) .&. (pApp \"q\" []) .|. (pApp \"r\" [])",
                      "((pApp \"p\" []) .&. (pApp \"q\" [])) .|. (pApp \"r\" [])",
                      "(pApp \"p\" []) .&. ((.~.)(pApp \"q\" []))",
                      "for_all (fromString (\"x\")) ((pApp \"p\" []) .&. (pApp \"q\" []))"]
          fms :: [formula]
          fms = [(p .&. q .|. r),
                 (p .&. (q .|. r)),
                 ((p .&. q) .|. r),
                 (p .&. ((.~.) q)),
                 (for_all "x" (p .&. q))]
          p = pApp "p" []
          q = pApp "q" []
          r = pApp "r" []
-}
