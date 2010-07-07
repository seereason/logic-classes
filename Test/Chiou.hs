{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings, RankNTypes, TypeSynonymInstances #-}
{-# OPTIONS -Wall -Werror -fno-warn-name-shadowing -fno-warn-orphans #-}
module Test.Chiou (tests, V(..)) where

import qualified Chiou.FirstOrderLogic as C
import Data.String (IsString(..))
import qualified Logic.Instances.Parameterized as P
import Logic.Instances.Chiou (AtomicFunction(..))
import Logic.Logic (Logic(..))
import Logic.Predicate (PredicateLogic(..), convertPred, showForm {-, toPropositional, InfixPred(..), freeVars, substitute-})
import Test.HUnit

-- | Variable names
newtype V = V String
    deriving (Eq,Ord) -- ,Data,Typeable,Read,Monoid,IsString

instance Show V where
    -- It looks more like logic with out the quotes, but you can't
    -- paste it back into your haskell program.
    show (V s) = show s 

instance IsString V where
    fromString = V

instance Show (P.Formula V String String) where
    show = showForm

type Sentence = C.Sentence V String AtomicFunction
type FormulaPF = P.Formula V String String

{-
instance Show V where
    show (V s) = show s

-- |Generate a series of variable names.  We *only* recognize variable
-- names which begin with one of the letters t thru z followed by zero
-- or more digits.
instance Enum V where
    succ v =
        toEnum (if n < cnt then n + 1 else if n == cnt then ord pref + cnt else n + cnt)
            where n = fromEnum v
    fromEnum (V s) =
        case break (not . isDigit) (reverse s) of
          ("", [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn
          (n, [c]) | ord c >= ord mn && ord c <= ord mx -> ord c - ord mn + cnt * (read (reverse n) :: Int)
          _ -> error $ "Invalid variable name: " ++ show s
    toEnum n =
        V (chr (ord mn + pre) : if suf == 0 then "" else show suf)
        where (suf, pre) = divMod n cnt

mn = 'x'
pref = 'x'
mx = 'z'
cnt = ord mx - ord mn + 1

instance Version V
$(deriveSerialize ''V)
$(deriveNewData [''V])
-}

-- |Argument to conversion tests.  These pairs look the same, but
-- they use the class methods to construct different types, as
-- you can see from the signature.
testFormulas ::[(String, Sentence, FormulaPF)]
testFormulas =
    [ ( "exists, equal"
      , exists ["x"] (x .=. y)
      , exists ["x"] (x .=. y))
    , ( "fApp"
      , (s [fApp (fromString "a") [x, y]])
      , (s [fApp (fromString "a") [x, y]]))
    , ( "forall, imply, and, var, pApp"
     , for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x]))
     , for_all ["x"] (((s [x] .=>. h [x]) .&. (h [x] .=>. m [x])) .=>. (s [x] .=>. m [x])))]
    where

x :: (PredicateLogic formula term v p f, IsString v) => term
x = var (fromString "x")
y :: (PredicateLogic formula term v p f, IsString v) => term
y = var (fromString "y")

s :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
s = pApp (fromString "s")
m :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
m = pApp (fromString "m")
h :: (PredicateLogic formula term v p f, IsString p) => [term] -> formula
h = pApp (fromString "h")

pairTest :: (String, Sentence, FormulaPF) -> [Test]
pairTest (s, f1, f2) =
    [ TestCase (assertEqual (s ++ ", Chiou to FormulaPF") f1 (convertPred id pc AtomicFunction f2)),
      TestCase (assertEqual (s ++ ", FormulaPF to Chiou") f2 (convertPred id pc fc f1)) ]

tests :: [Test]
tests = concatMap pairTest testFormulas

pc :: String -> String
pc = id

fc :: AtomicFunction -> String
fc (AtomicFunction s) = s
fc (AtomicSkolemFunction n) = show n
