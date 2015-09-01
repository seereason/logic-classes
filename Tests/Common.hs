-- |Types to use for creating test cases.  These are used in the Logic
-- package test cases, and are exported for use in its clients.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, StandaloneDeriving, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Common
    ( render
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
    , doTest, doExpected
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
import Data.Logic.Classes.FirstOrder (FirstOrderFormula, convertFOF, prettyFirstOrder)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Pretty (Pretty(pPrint))
import Data.Logic.Classes.Propositional (PropositionalFormula)
import qualified Data.Logic.Classes.Skolem as C
import Data.Logic.Classes.Term (Term(vt, fApp, foldTerm), Function)
import Data.Logic.Classes.Variable (Variable(..))
import Data.Logic.Harrison.Normal (trivial)
import Data.Logic.Harrison.Skolem (Skolem, skolemize, runSkolem, pnf, nnf, simplify)
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (SetOfSupport)
import qualified Data.Logic.Types.FirstOrder as P
import qualified Data.Set as S
import Data.String (IsString(fromString))
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode), (<>))

--import PropLogic (PropForm)

import Test.HUnit
import Text.PrettyPrint (Doc, text)

-- | Render a Pretty instance in single line mode
render :: Pretty a => a -> String
render = renderStyle (style {mode = OneLineMode}) . pPrint

newtype V = V String deriving (Eq, Ord, Data, Typeable)

instance IsString V where
    fromString = V

instance Show V where
    show (V s) = show s

prettyV :: V -> Doc
prettyV (V s) = text s

instance Pretty V where
    pPrint = prettyV

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
    asBool T = Just True
    asBool F = Just False
    asBool _ = Nothing

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

prettyP :: Pr -> Doc
prettyP T = prettyBool True
prettyP F = prettyBool False
prettyP Equals = text ".=."
prettyP (Pr s) = text s

instance Pretty Pr where
    pPrint = prettyP

data AtomicFunction
    = Fn String
    | Skolem V
    deriving (Eq, Ord, Data, Typeable)

instance Function AtomicFunction V

instance C.Skolem AtomicFunction V where
    toSkolem = Skolem
    isSkolem (Skolem _) = True
    isSkolem _ = False

instance IsString AtomicFunction where
    fromString = Fn

instance Show AtomicFunction where
    show (Fn s) = show s
    show (Skolem v) = "(toSkolem " ++ show v ++ ")"

prettyF :: AtomicFunction -> Doc
prettyF (Fn s) = text s
prettyF (Skolem v) = text "sK" <> pPrint v

instance Pretty AtomicFunction where
    pPrint = prettyF

type TFormula = P.Formula V Pr AtomicFunction
type TAtom = P.Predicate Pr TTerm
type TTerm = P.PTerm V AtomicFunction

{-
instance Pretty TFormula where
    pPrint = prettyFirstOrder (const pPrint) pPrint 0
-}

-- |This allows you to use an expression that returns the Doc type in a
-- unit test, such as prettyFirstOrder.  (This instance actually appears
-- in version 1.1.1.2.  Maybe should have been a C-bump.)
#if !MIN_VERSION_pretty(1,1,2)
instance Eq Doc where
    a == b = show a == show b
#endif

data TestFormula formula atom v
    = TestFormula
      { formula :: formula
      , name :: String
      , expected :: [Expected formula atom v]
      } -- deriving (Data, Typeable)

-- |Some values that we might expect after transforming the formula.
data Expected formula atom v
    = FirstOrderFormula formula
    | SimplifiedForm formula
    | NegationNormalForm formula
    | PrenexNormalForm formula
    | SkolemNormalForm formula
    | SkolemNumbers (S.Set AtomicFunction)
    | ClauseNormalForm (S.Set (S.Set formula))
    | TrivialClauses [(Bool, (S.Set formula))]
    | ConvertToChiou (Ch.Sentence V Pr AtomicFunction)
    | ChiouKB1 (Proof formula)
    | PropLogicSat Bool
    | SatSolverCNF CNF
    | SatSolverSat Bool
    -- deriving (Data, Typeable)

deriving instance Show (Ch.Sentence V Pr AtomicFunction)
deriving instance Show (Ch.CTerm V AtomicFunction)

type TTestFormula = TestFormula TFormula TAtom V

doTest :: TTestFormula -> Test
doTest (TestFormula formula name expected) =
    TestLabel name $ TestList $
    map (doExpected formula name) expected

doExpected formula name expected@(FirstOrderFormula f') = let label = (name ++ " original formula") in TestLabel label (TestCase (assertEqual label (p f') (p formula)))
doExpected formula name expected@(SimplifiedForm f') = let label = (name ++ " simplified") in TestLabel label (TestCase (assertEqual label (p f') (p (simplify formula))))
doExpected formula name expected@(PrenexNormalForm f') = let label = (name ++ " prenex normal form") in TestLabel label (TestCase (assertEqual label (p f') (p (pnf formula))))
doExpected formula name expected@(NegationNormalForm f') = let label = (name ++ " negation normal form") in TestLabel label (TestCase (assertEqual label (p f') (p (nnf . simplify $ formula))))
doExpected formula name expected@(SkolemNormalForm f') = let label = (name ++ " skolem normal form") in TestLabel label (TestCase (assertEqual label (p f') (p (runSkolem (skolemize id formula :: Skolem V (P.PTerm V AtomicFunction) TFormula)))))
doExpected formula name expected@(SkolemNumbers f') = let label = (name ++ " skolem numbers") in TestLabel label (TestCase (assertEqual label f' (skolemSet (runSkolem (skolemize id formula :: Skolem V (P.PTerm V AtomicFunction) TFormula)))))
doExpected formula name expected@(ClauseNormalForm fss) = let label = (name ++ " clause normal form") in TestLabel label (TestCase (assertEqual label fss (S.map (S.map p) (runSkolem (clauseNormalForm formula)))))
doExpected formula name expected@(TrivialClauses flags) = let label = (name ++ " trivial clauses") in TestLabel label (TestCase (assertEqual label flags (map (\ (x :: S.Set TFormula) -> (trivial x, x)) (S.toList (runSkolem (clauseNormalForm (formula :: TFormula)))))))
doExpected formula name expected@(ConvertToChiou result) =
          -- We need to convert formula to Chiou and see if it matches result.
          let ca :: TAtom -> Ch.Sentence V Pr AtomicFunction
              -- ca = undefined
              ca (P.Apply p ts) = Ch.Predicate p (map ct ts)
              ca (P.Equal t1 t2) = Ch.Equal (ct t1) (ct t2)
              ct :: TTerm -> Ch.CTerm V AtomicFunction
              ct = foldTerm cv fn
              cv :: V -> Ch.CTerm V AtomicFunction
              cv = vt
              fn :: AtomicFunction -> [TTerm] -> Ch.CTerm V AtomicFunction
              fn f ts = fApp f (map ct ts) in
          let label = (name ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual label result (convertFOF ca id formula :: Ch.Sentence V Pr AtomicFunction)))
doExpected formula name expected@(ChiouKB1 result) = let label = (name ++ " Chiou KB") in TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB [formula] >>= return . head))))
doExpected formula name expected@(PropLogicSat result) = let label = (name ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual label result (runSkolem (plSat formula))))
doExpected formula name expected@(SatSolverCNF result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label (norm result) (runNormal (SS.toCNF formula))))
doExpected formula name expected@(SatSolverSat result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label result ((null :: [a] -> Bool) (runNormalT (SS.toCNF formula >>= satisfiable)))))

p = id

norm = map S.toList . S.toList . S.fromList . map S.fromList

{-
skolemNormalForm' f = (skolem' . nnf . simplify $ f) >>= return . prenex' . nnf' . simplify'

-- skolem' :: formula -> SkolemT v term m pf
skolem' :: ( Monad m
           , Variable v
           , Term term v f
           , FirstOrderFormula formula atom v
           -- , Atom atom term v
           -- , PropositionalFormula pf atom
           -- , Formula formula term v
           ) =>
           formula -> SkolemT v term m pf
skolem' = undefined
-}

skolemSet :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Data formula) => formula -> S.Set f
skolemSet =
    foldr ins S.empty . skolemList
    where
      ins :: f -> S.Set f -> S.Set f
      ins f s = if C.isSkolem f
                then S.insert f s
                else s
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
                                            PropositionalFormula formula atom,
                                            AtomEq atom p term, atom ~ P.Predicate p (P.PTerm v f),
                                            Term term v f, term ~ P.PTerm v f,
                                            Literal formula atom,
                                            Ord formula, Data formula, Eq term, Show term, Show v, Show formula, Constants p, Eq p, Ord f, Show f) =>
           TestProof formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected :: ProofExpected formula v term -> [Test]
      doExpected (ChiouResult result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover") in
           TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB kb >> theoremKB c))))]
      doExpected (ChiouKB result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base") in
           TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB kb >> getKB))))]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula
