-- |Types to use for creating test cases.  These are used in the Logic
-- package test cases, and are exported for use in its clients.
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts, FlexibleInstances, RankNTypes, ScopedTypeVariables, StandaloneDeriving, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Data.Logic.Tests.Common
    ( myTest
      -- * Formula parameter types
    , V(..)
    , Pr(..)
    , AtomicFunction(..)
    , TFormula
    , TAtom
    , TTerm
    , TTestFormula
    , prettyV
    , prettyP
    , prettyF
      -- * Test case types
    , TestFormula(..)
    , Expected(..)
    , doTest
    , TestProof(..)
    , TTestProof
    , ProofExpected(..)
    , doProof
    ) where

import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Boolean.SatSolver (CNF)
import Data.Char (isDigit)
import Data.Generics (Data, Typeable, listify)
import Data.Logic.Classes.Apply (Predicate)
import Data.Logic.Classes.Arity (Arity(arity))
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(satisfiable))
import Data.Logic.Classes.Constants (Constants(..), prettyBool)
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula, convertFOF)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Pretty (Pretty(pretty))
import Data.Logic.Classes.Skolem (Skolem(..))
import Data.Logic.Classes.Term (Term(vt, fApp, foldTerm), Function)
import Data.Logic.Classes.Variable (Variable(..))
import Data.Logic.Harrison.Normal (trivial)
import Data.Logic.Harrison.Skolem (skolemNormalForm, runSkolem, pnf, nnf, simplify)
import qualified Data.Logic.Instances.Chiou as C
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (SetOfSupport)
import qualified Data.Logic.Types.FirstOrder as P
import qualified Data.Set as S
import Data.String (IsString(fromString))

--import PropLogic (PropForm)

import Test.HUnit
import Text.PrettyPrint (Doc, text)

myTest :: (Show a, Eq a) => String -> a -> a -> Test
myTest label expected input =
    TestLabel label $ TestCase (assertEqual label expected input)

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

prettyV :: V -> Doc
prettyV (V s) = text s

instance Pretty V where
    pretty = prettyV

instance Variable V where
    prefix p (V s) = V (p ++ s)
    variant x@(V s) xs = if S.member x xs then variant (V (next s)) xs else x
    prettyVariable (V s) = text s

next :: String -> String
next s =
    case break (not . isDigit) (reverse s) of
      (_, "") -> "x"
      ("", nondigits) -> nondigits ++ "2"
      (digits, nondigits) -> nondigits ++ show (1 + read (reverse digits) :: Int)

-- |A newtype for the Primitive Predicate parameter.
data Pr
    = Pr String
    | T
    | F
    | Equals
    deriving (Eq, Ord, Data, Typeable)

instance Predicate Pr

instance IsString Pr where
    fromString = Pr

instance Constants Pr where
    fromBool True = T
    fromBool False = F

instance Arity Pr where
    arity (Pr _) = Nothing
    arity T = Just 0
    arity F = Just 0
    arity Equals = Just 2

instance Show Pr where
    show T = "fromBool True"
    show F = "fromBool False"
    show Equals = ".=."
    show (Pr s) = show s            -- Because Pr is an instance of IsString

instance Pretty Pr where
    pretty (Pr s) = text s
    pretty T = prettyBool True
    pretty F = prettyBool False
    pretty Equals = text "="

prettyP :: Pr -> Doc
prettyP T = text "True"
prettyP F = text "False"
prettyP Equals = text ".=."
prettyP (Pr s) = text s

data AtomicFunction
    = Fn String
    | Skolem Int
    deriving (Eq, Ord, Data, Typeable)

instance Function AtomicFunction

instance Skolem AtomicFunction where
    toSkolem = Skolem
    fromSkolem (Skolem n) = Just n
    fromSkolem _ = Nothing

instance IsString AtomicFunction where
    fromString = Fn

instance Show AtomicFunction where
    show (Fn s) = show s
    show (Skolem n) = "toSkolem " ++ show n

instance Pretty AtomicFunction where
    pretty (Fn s) = text s
    pretty (Skolem n) = text ("Sk" ++ show n)

prettyF :: AtomicFunction -> Doc
prettyF (Fn s) = text s
prettyF (Skolem n) = text ("sK" ++ show n)

type TFormula = P.Formula V Pr AtomicFunction
type TAtom = P.Predicate Pr TTerm
type TTerm = P.PTerm V AtomicFunction

deriving instance Show (P.PTerm V AtomicFunction)
deriving instance Show (P.Predicate Pr (P.PTerm V AtomicFunction))
deriving instance Show TFormula

-- |This allows you to use an expression that returns the Doc type in a
-- unit test, such as prettyFirstOrder.
instance Eq Doc where
    a == b = show a == show b

data (formula ~ TFormula, atom ~ TAtom, v ~ V) => TestFormula formula atom v
    = TestFormula
      { formula :: formula
      , name :: String
      , expected :: [Expected formula atom v]
      } -- deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data (FirstOrderFormula formula atom v, formula ~ TFormula, atom ~ TAtom, v ~ V) => Expected formula atom v
    = FirstOrderFormula formula
    | SimplifiedForm formula
    | NegationNormalForm formula
    | PrenexNormalForm formula
    | SkolemNormalForm formula
    | SkolemNumbers (S.Set Int)
    | ClauseNormalForm (S.Set (S.Set formula))
    | TrivialClauses [(Bool, (S.Set formula))]
    | ConvertToChiou (C.Sentence V Pr AtomicFunction)
    | ChiouKB1 (Proof formula)
    | PropLogicSat Bool
    | SatSolverCNF CNF
    | SatSolverSat Bool
    -- deriving (Data, Typeable)

deriving instance Show (C.Sentence V Pr AtomicFunction)
deriving instance Show (C.CTerm V AtomicFunction)

type TTestFormula = TestFormula TFormula TAtom V

doTest :: TTestFormula -> Test
doTest f =
    TestLabel (name f) $ TestList $ 
    map doExpected (expected f)
    where
      doExpected (FirstOrderFormula f') =
          myTest (name f ++ " original formula") (p f') (p (formula f))
      doExpected (SimplifiedForm f') =
          myTest (name f ++ " simplified") (p f') (p (simplify (formula f)))
      doExpected (PrenexNormalForm f') =
          myTest (name f ++ " prenex normal form") (p f') (p (pnf (formula f)))
      doExpected (NegationNormalForm f') =
          myTest (name f ++ " negation normal form") (p f') (p (nnf . simplify $ (formula f)))
      doExpected (SkolemNormalForm f') =
          myTest (name f ++ " skolem normal form") (p f') (p (runSkolem (skolemNormalForm (formula f))))
      doExpected (SkolemNumbers f') =
          myTest (name f ++ " skolem numbers") f' (skolemSet (runSkolem (skolemNormalForm (formula f))))
      doExpected (ClauseNormalForm fss) =
          myTest (name f ++ " clause normal form") fss (S.map (S.map p) (runSkolem (clauseNormalForm (formula f))))
      doExpected (TrivialClauses flags) =
          myTest (name f ++ " trivial clauses") flags (map (\ (x :: S.Set TFormula) -> (trivial x, x)) (S.toList (runSkolem (clauseNormalForm (formula f :: TFormula)))))
      doExpected (ConvertToChiou result) =
          -- We need to convert (formula f) to Chiou and see if it matches result.
          let ca :: TAtom -> C.Sentence V Pr AtomicFunction
              -- ca = undefined
              ca (P.Apply p ts) = C.Predicate p (map ct ts)
              ca (P.Equal t1 t2) = C.Equal (ct t1) (ct t2)
              ct :: TTerm -> C.CTerm V AtomicFunction
              ct = foldTerm cv fn
              cv :: V -> C.CTerm V AtomicFunction
              cv = vt
              fn :: AtomicFunction -> [TTerm] -> C.CTerm V AtomicFunction
              fn f ts = fApp f (map ct ts) in
          myTest (name f ++ " converted to Chiou") result (convertFOF ca id (formula f) :: C.Sentence V Pr AtomicFunction)
      doExpected (ChiouKB1 result) =
          myTest (name f ++ " Chiou KB") result (runProver' Nothing (loadKB [formula f] >>= return . head))
      doExpected (PropLogicSat result) =
          myTest (name f ++ " PropLogic.satisfiable") result (runSkolem (plSat (formula f)))
      doExpected (SatSolverCNF result) =
          myTest (name f ++ " SatSolver CNF") (norm result) (runNormal (SS.toCNF (formula f)))
      doExpected (SatSolverSat result) =
          myTest (name f ++ " SatSolver CNF") result (null (runNormalT (SS.toCNF (formula f) >>= satisfiable)))
      p = id

      norm = map S.toList . S.toList . S.fromList . map S.fromList

skolemSet :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Data formula) => formula -> S.Set Int
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins :: f -> S.Set Int -> S.Set Int
      ins f s = case fromSkolem f of
                  Just n -> S.insert n s
                  Nothing -> s
      skolemList :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . map return . listify (const True)

data TestProof formula term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [formula])
      , conjecture :: formula
      , proofExpected :: [ProofExpected formula v term]
      } deriving (Data, Typeable)

type TTestProof = TestProof TFormula TTerm V

data ProofExpected formula v term
    = ChiouResult (Bool, SetOfSupport formula v term)
    | ChiouKB (S.Set (WithId (ImplicativeForm formula)))
    deriving (Data, Typeable)

doProof :: forall formula atom term v p f. (FirstOrderFormula formula atom v,
                                            AtomEq atom p term, atom ~ P.Predicate p (P.PTerm v f),
                                            Term term v f, term ~ P.PTerm v f,
                                            Literal formula atom v,
                                            Ord formula, Data formula, Eq term, Show term, Show v, Show formula, Constants p, Eq p, Ord f, Show f) =>
           TestProof formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected :: ProofExpected formula v term -> [Test]
      doExpected (ChiouResult result) =
          [myTest (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover")
                  result
                  (runProver' Nothing (loadKB kb >> theoremKB c))]
      doExpected (ChiouKB result) =
          [myTest (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base")
                  result
                  (runProver' Nothing (loadKB kb >> getKB))]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula
