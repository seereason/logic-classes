-- |Types to use for creating test cases.  These are used in the Logic
-- package test cases, and are exported for use in its clients.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, StandaloneDeriving, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Common
    ( render
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
import Data.Generics (Data, Typeable, listify)
import Data.List as List (foldr, map, null)
#if 1
import Data.Logic hiding (Skolem)
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Harrison.Skolem (Skolem, skolemize, runSkolem, pnf, nnf, simplify)
import Data.Logic.Harrison.Normal (trivial)
import qualified Data.Logic.Types.FirstOrder as P
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(satisfiable))
import Data.Logic.Instances.PropLogic (plSat)
import Data.Logic.Resolution (SetOfSupport)
#else
import Data.Logic.Classes.ClauseNormalForm (ClauseNormalFormula(satisfiable))
import Data.Logic.Classes.Constants (Constants(..))
import Data.Logic.Classes.Equals (AtomEq)
import Data.Logic.Classes.FirstOrder (FirstOrderFormula, convertFOF)
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Pretty (Pretty(pPrint))
import Data.Logic.Classes.Propositional (PropositionalFormula)
import qualified Data.Logic.Classes.Skolem as C
import Data.Logic.Harrison.Normal (trivial)
import Data.Logic.Harrison.Skolem (Skolem, skolemize, runSkolem, pnf, nnf, simplify)
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.Instances.Test
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Clause (clauseNormalForm)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (SetOfSupport)
import qualified Data.Logic.Types.FirstOrder as P
#endif
import Data.Set as Set
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode))

--import PropLogic (PropForm)

import Test.HUnit

-- | Render a Pretty instance in single line mode
render :: Pretty a => a -> String
render = renderStyle (style {mode = OneLineMode}) . pPrint

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
    | SkolemNumbers (Set AtomicFunction)
    | ClauseNormalForm (Set (Set formula))
    | TrivialClauses [(Bool, (Set formula))]
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
    List.map (doExpected formula name) expected

doExpected formula name expected@(FirstOrderFormula f') = let label = (name ++ " original formula") in TestLabel label (TestCase (assertEqual label f' formula))
doExpected formula name expected@(SimplifiedForm f') = let label = (name ++ " simplified") in TestLabel label (TestCase (assertEqual label f' (simplify formula)))
doExpected formula name expected@(PrenexNormalForm f') = let label = (name ++ " prenex normal form") in TestLabel label (TestCase (assertEqual label f' (pnf formula)))
doExpected formula name expected@(NegationNormalForm f') = let label = (name ++ " negation normal form") in TestLabel label (TestCase (assertEqual label f' (nnf . simplify $ formula)))
doExpected formula name expected@(SkolemNormalForm f') = let label = (name ++ " skolem normal form") in TestLabel label (TestCase (assertEqual label f' (runSkolem (skolemize id formula :: Skolem V (P.PTerm V AtomicFunction) TFormula))))
doExpected formula name expected@(SkolemNumbers f') = let label = (name ++ " skolem numbers") in TestLabel label (TestCase (assertEqual label f' (skolemSet (runSkolem (skolemize id formula :: Skolem V (P.PTerm V AtomicFunction) TFormula)))))
doExpected formula name expected@(ClauseNormalForm fss) =
    let label = (name ++ " clause normal form") in
    TestLabel label (TestCase (assertEqual label
                                           (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (fss :: (Set (Set TFormula)))))
                                           (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (Set.map (Set.map id) (runSkolem (clauseNormalForm formula)) :: Set (Set TFormula))))))
doExpected formula name expected@(TrivialClauses flags) = let label = (name ++ " trivial clauses") in TestLabel label (TestCase (assertEqual label flags (List.map (\ (x :: Set TFormula) -> (trivial x, x)) (Set.toList (runSkolem (clauseNormalForm (formula :: TFormula)))))))
doExpected formula name expected@(ConvertToChiou result) =
          -- We need to convert formula to Chiou and see if it matches result.
          let ca :: TAtom -> Ch.Sentence V Pr AtomicFunction
              -- ca = undefined
              ca (P.Apply p ts) = Ch.Predicate p (List.map ct ts)
              ca (P.Equal t1 t2) = Ch.Equal (ct t1) (ct t2)
              ct :: TTerm -> Ch.CTerm V AtomicFunction
              ct = foldTerm cv fn
              cv :: V -> Ch.CTerm V AtomicFunction
              cv = vt
              fn :: AtomicFunction -> [TTerm] -> Ch.CTerm V AtomicFunction
              fn f ts = fApp f (List.map ct ts) in
          let label = (name ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual label result (convertFOF ca id formula :: Ch.Sentence V Pr AtomicFunction)))
doExpected formula name expected@(ChiouKB1 result) = let label = (name ++ " Chiou KB") in TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB [formula] >>= return . head))))
doExpected formula name expected@(PropLogicSat result) = let label = (name ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual label result (runSkolem (plSat formula))))
doExpected formula name expected@(SatSolverCNF result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label (norm result) (runNormal (SS.toCNF formula))))
doExpected formula name expected@(SatSolverSat result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label result ((List.null :: [a] -> Bool) (runNormalT (SS.toCNF formula >>= satisfiable)))))

-- p = id

norm = List.map Set.toList . Set.toList . Set.fromList . List.map Set.fromList

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

skolemSet :: forall formula atom term v p f. (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Data formula) => formula -> Set f
skolemSet =
    List.foldr ins Set.empty . skolemList
    where
      ins :: f -> Set f -> Set f
      ins f s = maybe s (const (Set.insert f s)) (fromSkolem f)
      skolemList :: (FirstOrderFormula formula atom v, AtomEq atom p term, Term term v f, Data f, Typeable f, Data formula) => formula -> [f]
      skolemList inf = gFind inf :: (Typeable f => [f])

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . List.map return . listify (const True)

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
    | ChiouKB (Set (WithId (ImplicativeForm formula)))
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
