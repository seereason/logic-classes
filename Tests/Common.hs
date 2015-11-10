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

import Apply (HasApply(TermOf, PredOf), Predicate)
import Control.Monad.Identity (Identity)
import Control.Monad.Reader (MonadPlus(..), msum)
import qualified Data.Boolean as B (CNF, Literal)
import Data.Generics (Data, Typeable, listify)
import Data.List as List (map, null)
import Data.Logic.Classes.Atom (Atom(..))
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (ProverT')
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (getSubstAtomEq, isRenameOfAtomEq, SetOfSupport)
import Data.Set as Set
import Equate (HasEquate(foldEquate))
import FOL (asubst, fva, IsFirstOrder)
import Formulas (IsFormula(AtomOf))
import Lit (convertLiteral, LFormula)
import Pretty (assertEqual', Pretty(pPrint))
import Prop (convertPropositional, PFormula, satisfiable, trivial)
import PropLogic (PropForm)
import Quantified (convertQuantified, IsQuantified(..))
import Skolem (Function, SkAtom, SkTerm, SkolemT, Formula, simpcnf', simpdnf', HasSkolem(SVarOf),
               nnf, pnf, runSkolem, simplify, skolemize, skolems)
import Term (fApp, foldTerm, IsTerm(FunOf, TVarOf), V, vt)
import Test.HUnit
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode))

instance Atom SkAtom SkTerm V where
    substitute = asubst
    freeVariables = fva
    allVariables = fva -- Variables are always free in an atom - this method is unnecessary
    unify = unify
    match = unify
    foldTerms f r pr = foldEquate (\t1 t2 -> f t2 (f t1 r)) (\_ ts -> Prelude.foldr f r ts) pr
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq

instance IsFirstOrder (PropForm SkAtom)

-- | We shouldn't need this instance, but right now we need ot to use
-- convertFirstOrder.  The conversion functions need work.
instance IsQuantified (PropForm SkAtom) where
    type VarOf (PropForm SkAtom) = V
    quant _ _ _ = error "FIXME: IsQuantified (PropForm SkAtom) SkAtom V"
    foldQuantified = error "FIXME: IsQuantified (PropForm SkAtom) SkAtom V"

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
    | SkolemNormalForm (PFormula SkAtom)
    | SkolemNumbers (Set Function)
    | ClauseNormalForm (Set (Set (LFormula atom)))
    | DisjNormalForm (Set (Set (LFormula atom)))
    | TrivialClauses [(Bool, (Set formula))]
    | ConvertToChiou (Ch.Sentence V Predicate Function)
    | ChiouKB1 (Proof (LFormula atom))
    | PropLogicSat Bool
    | SatSolverCNF B.CNF
    | SatSolverSat Bool
    -- deriving (Data, Typeable)

type TTestFormula = TestFormula Formula SkAtom V

doTest :: TTestFormula -> Test
doTest (TestFormula fm nm expect) =
    TestLabel nm $ TestList $
    List.map doExpected expect
    where
      doExpected :: Expected Formula SkAtom V -> Test
      doExpected (FirstOrderFormula f') = let label = (nm ++ " original formula") in TestLabel label (TestCase (assertEqual' label f' fm))
      doExpected (SimplifiedForm f') = let label = (nm ++ " simplified") in TestLabel label (TestCase (assertEqual' label f' (simplify fm)))
      doExpected (PrenexNormalForm f') = let label = (nm ++ " prenex normal form") in TestLabel label (TestCase (assertEqual' label f' (pnf fm)))
      doExpected (NegationNormalForm f') = let label = (nm ++ " negation normal form") in TestLabel label (TestCase (assertEqual' label f' (nnf . simplify $ fm)))
      doExpected (SkolemNormalForm f') = let label = (nm ++ " skolem normal form") in TestLabel label (TestCase (assertEqual' label f' (runSkolem (skolemize id fm :: SkolemT Identity Function (PFormula SkAtom)))))
      doExpected (SkolemNumbers f') = let label = (nm ++ " skolem numbers") in TestLabel label (TestCase (assertEqual' label f' (skolems (runSkolem (skolemize id fm :: SkolemT Identity Function (PFormula SkAtom))))))
      doExpected (ClauseNormalForm fss) =
          let label = (nm ++ " clause normal form") in
          TestLabel label (TestCase (assertEqual' label
                                                 ((List.map (List.map (convertLiteral id)) . Set.toList . Set.map Set.toList $ fss) :: [[Formula]])
                                                 ((Set.toList . Set.map (Set.toList) . simpcnf' . (convertPropositional id :: PFormula SkAtom -> Formula) . runSkolem . skolemize id $ fm) :: [[Formula]])))
              where
                convert :: PFormula SkAtom -> Formula
                convert = undefined -- ((convertLiteral id) :: LFormula SkAtom -> Formula)
      doExpected (DisjNormalForm fss) =
          let label = (nm ++ " disjunctive normal form") in
          TestLabel label (TestCase (assertEqual' label
                                                 ((List.map (List.map (convertLiteral id)) . Set.toList . Set.map Set.toList $ fss) :: [[Formula]])
                                                 ((Set.toList . Set.map (Set.toList) . simpdnf' . (convertPropositional id :: PFormula SkAtom -> Formula) . runSkolem . skolemize id $ fm) :: [[Formula]])))
      doExpected (TrivialClauses flags) = let label = (nm ++ " trivial clauses") in TestLabel label (TestCase (assertEqual' label flags (List.map (\ (x :: Set Formula) -> (trivial x, x)) (Set.toList (simpcnf' (fm :: Formula))))))
      doExpected (ConvertToChiou result) =
                -- We need to convert formula to Chiou and see if it matches result.
                let ca :: SkAtom -> Ch.Sentence V Predicate Function
                    -- ca = undefined
                    ca = foldEquate (\t1 t2 -> Ch.Equal (ct t1) (ct t2)) (\p ts -> Ch.Predicate p (List.map ct ts))
                    ct :: SkTerm -> Ch.CTerm V Function
                    ct = foldTerm cv fn
                    cv :: V -> Ch.CTerm V Function
                    cv = vt
                    fn :: Function -> [SkTerm] -> Ch.CTerm V Function
                    fn f ts = fApp f (List.map ct ts) in
                let label = (nm ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual' label result (convertQuantified ca id fm :: Ch.Sentence V Predicate Function)))
      doExpected (ChiouKB1 result) = let label = (nm ++ " Chiou KB") in TestLabel label (TestCase (assertEqual' label result ((runProver' Nothing (loadKB [fm] >>= return . head)) :: (Proof (LFormula SkAtom)))))
      doExpected (PropLogicSat result) = let label = (nm ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual' label result (plSat (runSkolem (skolemize id fm)))))
      doExpected (SatSolverCNF result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual' label (norm result) (runNormal (SS.toCNF fm))))
      doExpected (SatSolverSat result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual' label result ((List.null :: [a] -> Bool) (runNormalT (SS.toCNF fm >>= return . satisfiable)))))

-- p = id

norm :: [[B.Literal]] -> [[B.Literal]]
norm = List.map Set.toList . Set.toList . Set.fromList . List.map Set.fromList

-- | @gFind a@ will extract any elements of type @b@ from
-- @a@'s structure in accordance with the MonadPlus
-- instance, e.g. Maybe Foo will return the first Foo
-- found while [Foo] will return the list of Foos found.
gFind :: (MonadPlus m, Data a, Typeable b) => a -> m b
gFind = msum . List.map return . listify (const True)

data TestProof fof atom term v
    = TestProof
      { proofName :: String
      , proofKnowledge :: (String, [fof])
      , conjecture :: fof
      , proofExpected :: [ProofExpected (LFormula atom) v term]
      } deriving (Data, Typeable)

type TTestProof = TestProof Formula SkAtom SkTerm V

data ProofExpected lit v term
    = ChiouResult (Bool, SetOfSupport lit v term)
    | ChiouKB (Set (WithId (ImplicativeForm lit)))
    deriving (Data, Typeable)

doProof :: forall formula lit atom term v function.
           (IsFirstOrder formula, Ord formula, Pretty formula,
            lit ~ LFormula atom,
            HasEquate atom,
            Atom atom term v,
            HasSkolem function,
            Eq formula, Eq term, Eq v, Ord term, Show formula, Show term, Show v,
            Data lit, Data atom, Data formula, Typeable function,
            atom ~ AtomOf formula, term ~ TermOf atom, function ~ FunOf term,
            v ~ TVarOf term, v ~ SVarOf function) =>
           TestProof formula atom term v -> Test
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
           (atom ~ AtomOf formula, v ~ TVarOf term, v ~ SVarOf f, term ~ TermOf atom, p ~ PredOf atom, f ~ FunOf term,
            lit ~ LFormula atom,
            Monad m, Data formula, Data atom,
            IsFirstOrder formula, Ord formula, Pretty formula,
            HasEquate atom,
            HasSkolem f,
            Atom atom term v,
            IsTerm term, Typeable f) => [formula] -> ProverT' v term lit m [Proof lit]
loadKB' = loadKB

theoremKB' :: forall m formula lit atom p term v f.
              (atom ~ AtomOf formula, v ~ TVarOf term, v ~ SVarOf f, term ~ TermOf atom, p ~ PredOf atom, f ~ FunOf term,
               lit ~ LFormula atom,
               Monad m, Data formula, Data atom,
               IsFirstOrder formula, Ord formula, Pretty formula,
               HasEquate atom,
               HasSkolem f,
               Atom atom term v,
               IsTerm term, Typeable f
              ) => formula -> ProverT' v term lit m (Bool, SetOfSupport lit v term)
theoremKB' = theoremKB
