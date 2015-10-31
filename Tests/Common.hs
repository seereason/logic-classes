-- |Types to use for creating test cases.  These are used in the Logic
-- package test cases, and are exported for use in its clients.
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, StandaloneDeriving, TypeFamilies, TypeSynonymInstances, UndecidableInstances #-}
{-# OPTIONS -Wwarn #-}
module Common
    ( render
    , TestFormula(..)
    , Expected(..)
    , doTest
    , TestProof(..)
    , TTestProof
    , ProofExpected(..)
    , doProof
    ) where

import Control.Monad.Identity (Identity)
import Control.Monad.Reader (MonadPlus(..), msum)
import qualified Data.Boolean as B (CNF, Literal)
import Data.Generics (Data, Typeable, listify)
import Data.List as List (map, null)
import Data.Logic.Classes.Atom (Atom(..))
import Data.Maybe (isJust)
import Skolem (fromSkolem, nnf, pnf, runSkolem, simplify, skolemize)
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (ProverT')
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (getSubstAtomEq, isRenameOfAtomEq, SetOfSupport)
import Data.Set as Set
import FOL (asubst, convertQuantified, fApp, foldTerm, funcs, fva,
            HasApply(TermOf, PredOf), HasApplyAndEquate(foldEquate),
            IsFirstOrder, IsQuantified(..), IsTerm(FunOf, TVarOf), Predicate, V, vt)
import Formulas (IsFormula(AtomOf))
import Lib (Marked)
import Pretty (assertEqual', Pretty(pPrint))
import Prop (PFormula, satisfiable, trivial, unmarkLiteral)
import Prop (Literal, unmarkPropositional)
import PropLogic (PropForm)
--import Safe (readMay)
import Skolem (Function, MyAtom, MyTerm, SkolemT, MyFormula, MyAtom, MyTerm, simpcnf', simpdnf', HasSkolem)
import Test.HUnit
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode))

instance Atom MyAtom MyTerm V where
    substitute = asubst
    freeVariables = fva
    allVariables = fva -- Variables are always free in an atom - this method is unnecessary
    unify = unify
    match = unify
    foldTerms f r pr = foldEquate (\t1 t2 -> f t2 (f t1 r)) (\_ ts -> Prelude.foldr f r ts) pr
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq

instance IsFirstOrder (PropForm MyAtom)

-- | We shouldn't need this instance, but right now we need ot to use
-- convertFirstOrder.  The conversion functions need work.
instance IsQuantified (PropForm MyAtom) where
    type VarOf (PropForm MyAtom) = V
    quant _ _ _ = error "FIXME: IsQuantified (PropForm MyAtom) MyAtom V"
    foldQuantified = error "FIXME: IsQuantified (PropForm MyAtom) MyAtom V"

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
    | SkolemNormalForm (PFormula MyAtom)
    | SkolemNumbers (Set Function)
    | ClauseNormalForm (Set (Set (Marked Literal formula)))
    | DisjNormalForm (Set (Set (Marked Literal formula)))
    | TrivialClauses [(Bool, (Set formula))]
    | ConvertToChiou (Ch.Sentence V Predicate Function)
    | ChiouKB1 (Proof (Marked Literal formula))
    | PropLogicSat Bool
    | SatSolverCNF B.CNF
    | SatSolverSat Bool
    -- deriving (Data, Typeable)

type TTestFormula = TestFormula MyFormula MyAtom V

doTest :: TTestFormula -> Test
doTest (TestFormula fm nm expect) =
    TestLabel nm $ TestList $
    List.map doExpected expect
    where
      doExpected :: Expected MyFormula MyAtom V -> Test
      doExpected (FirstOrderFormula f') = let label = (nm ++ " original formula") in TestLabel label (TestCase (assertEqual' label f' fm))
      doExpected (SimplifiedForm f') = let label = (nm ++ " simplified") in TestLabel label (TestCase (assertEqual' label f' (simplify fm)))
      doExpected (PrenexNormalForm f') = let label = (nm ++ " prenex normal form") in TestLabel label (TestCase (assertEqual' label f' (pnf fm)))
      doExpected (NegationNormalForm f') = let label = (nm ++ " negation normal form") in TestLabel label (TestCase (assertEqual' label f' (nnf . simplify $ fm)))
      doExpected (SkolemNormalForm f') = let label = (nm ++ " skolem normal form") in TestLabel label (TestCase (assertEqual' label f' (runSkolem (skolemize id fm :: SkolemT Identity (PFormula MyAtom)))))
      doExpected (SkolemNumbers f') = let label = (nm ++ " skolem numbers") in TestLabel label (TestCase (assertEqual' label f' (skolemSet (runSkolem (skolemize id fm :: SkolemT Identity (PFormula MyAtom))))))
      doExpected (ClauseNormalForm fss) =
          let label = (nm ++ " clause normal form") in
          TestLabel label (TestCase (assertEqual' label
                                                 ((List.map (List.map unmarkLiteral) . Set.toList . Set.map Set.toList $ fss) :: [[MyFormula]])
                                                 ((Set.toList . Set.map (Set.toList . Set.map unmarkPropositional) . simpcnf' . runSkolem . skolemize id $ fm) :: [[MyFormula]])))
      doExpected (DisjNormalForm fss) =
          let label = (nm ++ " disjunctive normal form") in
          TestLabel label (TestCase (assertEqual' label
                                                 ((List.map (List.map unmarkLiteral) . Set.toList . Set.map Set.toList $ fss) :: [[MyFormula]])
                                                 ((Set.toList . Set.map (Set.toList . Set.map unmarkPropositional) . simpdnf' . runSkolem . skolemize id $ fm) :: [[MyFormula]])))
      doExpected (TrivialClauses flags) = let label = (nm ++ " trivial clauses") in TestLabel label (TestCase (assertEqual' label flags (List.map (\ (x :: Set MyFormula) -> (trivial x, x)) (Set.toList (simpcnf' (fm :: MyFormula))))))
      doExpected (ConvertToChiou result) =
                -- We need to convert formula to Chiou and see if it matches result.
                let ca :: MyAtom -> Ch.Sentence V Predicate Function
                    -- ca = undefined
                    ca = foldEquate (\t1 t2 -> Ch.Equal (ct t1) (ct t2)) (\p ts -> Ch.Predicate p (List.map ct ts))
                    ct :: MyTerm -> Ch.CTerm V Function
                    ct = foldTerm cv fn
                    cv :: V -> Ch.CTerm V Function
                    cv = vt
                    fn :: Function -> [MyTerm] -> Ch.CTerm V Function
                    fn f ts = fApp f (List.map ct ts) in
                let label = (nm ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual' label result (convertQuantified ca id fm :: Ch.Sentence V Predicate Function)))
      doExpected (ChiouKB1 result) = let label = (nm ++ " Chiou KB") in TestLabel label (TestCase (assertEqual' label result ((runProver' Nothing (loadKB [fm] >>= return . head)) :: (Proof (Marked Literal MyFormula)))))
      doExpected (PropLogicSat result) = let label = (nm ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual' label result (plSat (runSkolem (skolemize id fm)))))
      doExpected (SatSolverCNF result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual' label (norm result) (runNormal (SS.toCNF fm))))
      doExpected (SatSolverSat result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual' label result ((List.null :: [a] -> Bool) (runNormalT (SS.toCNF fm >>= return . satisfiable)))))

-- p = id

norm :: [[B.Literal]] -> [[B.Literal]]
norm = List.map Set.toList . Set.toList . Set.fromList . List.map Set.fromList

skolemSet :: PFormula MyAtom -> Set Function
skolemSet = Set.filter (isJust . fromSkolem) . Set.map fst . funcs

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . List.map return . listify (const True)

data TestProof fof term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [fof])
      , conjecture :: fof
      , proofExpected :: [ProofExpected (Marked Literal fof) v term]
      } deriving (Data, Typeable)

type TTestProof = TestProof MyFormula MyTerm V

data ProofExpected lit v term
    = ChiouResult (Bool, SetOfSupport lit v term)
    | ChiouKB (Set (WithId (ImplicativeForm lit)))
    deriving (Data, Typeable)

doProof :: forall formula lit atom term v f.
           (atom ~ AtomOf formula, v ~ VarOf formula, v ~ TVarOf term, term ~ TermOf atom, f ~ FunOf term,
            IsFirstOrder formula, Ord formula, Pretty formula,
            HasApplyAndEquate atom,
            Atom atom term v,
            HasSkolem f v,
            lit ~ Marked Literal formula,
            Eq formula, Eq term, Eq v, Ord term, Show formula, Show term, Data formula, Typeable f, Show v
           ) => TestProof formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected :: ProofExpected lit v term -> [Test]
      doExpected (ChiouResult result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover") in
           TestLabel label (TestCase (assertEqual' label result (runProver' Nothing (loadKB' kb >> theoremKB' c))))]
      doExpected (ChiouKB result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base") in
           TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB kb >> getKB))))]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula

loadKB' :: forall m formula lit atom p term v f.
           (atom ~ AtomOf formula, v ~ VarOf formula, v ~ TVarOf term, term ~ TermOf atom, p ~ PredOf atom, f ~ FunOf term,
            lit ~ Marked Literal formula,
            Monad m, Data formula,
            IsFirstOrder formula, Ord formula, Pretty formula,
            HasApplyAndEquate atom,
            HasSkolem f v,
            Atom atom term v,
            IsTerm term, Typeable f) => [formula] -> ProverT' v term (ImplicativeForm lit) m [Proof lit]
loadKB' = loadKB

theoremKB' :: forall m formula lit atom p term v f.
              (atom ~ AtomOf formula, v ~ VarOf formula, v ~ TVarOf term, term ~ TermOf atom, p ~ PredOf atom, f ~ FunOf term,
               lit ~ Marked Literal formula,
               Monad m, Data formula,
               IsFirstOrder formula, Ord formula, Pretty formula,
               HasApplyAndEquate atom,
               HasSkolem f v,
               Atom atom term v,
               IsTerm term, Typeable f
              ) => formula -> ProverT' v term (ImplicativeForm lit) m (Bool, SetOfSupport lit v term)
theoremKB' = theoremKB
