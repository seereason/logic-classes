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

import Control.Monad.Identity (Identity)
import Control.Monad.Reader (MonadPlus(..), msum)
import Data.Boolean.SatSolver (CNF)
import Data.Generics (Data, Typeable, listify)
import Data.List as List (map, null)
import Data.Logic.Classes.Atom (Atom(..))
import Skolem (skolemize, runSkolem, pnf, nnf, simplify)
import qualified Data.Logic.Instances.Chiou as Ch
import Data.Logic.Instances.PropLogic (plSat)
import qualified Data.Logic.Instances.SatSolver as SS
import Data.Logic.KnowledgeBase (ProverT')
import Data.Logic.KnowledgeBase (WithId, runProver', Proof, loadKB, theoremKB, getKB)
import Data.Logic.Normal.Implicative (ImplicativeForm, runNormal, runNormalT)
import Data.Logic.Resolution (getSubstAtomEq, isRenameOfAtomEq, SetOfSupport)
import Data.Set as Set
import FOL (asubst, convertFirstOrder, fApp, foldEquals, foldTerm, fva, HasEquality,
            IsFirstOrder, IsQuantified, IsTerm, Predicate(NamedPredicate), V, vt)
import Formulas (IsCombinable, HasBoolean(fromBool, asBool), IsNegatable, IsFormula)
import Lit (IsLiteral)
import Pretty (Pretty(pPrint), HasFixity)
import Prop (IsPropositional, satisfiable, trivial)
import PropLogic (PropForm)
import Safe (readMay)
import Skolem (Function, MyAtom, MyTerm, SkolemT, MyFormula, MyAtom, MyTerm, simpcnf', HasSkolem(fromSkolem))
import Test.HUnit
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode))

instance Atom MyAtom MyTerm V where
    substitute = asubst
    freeVariables = fva
    allVariables = fva -- Variables are always free in an atom - this method is unnecessary
    unify = unify
    match = unify
    foldTerms f r pr = foldEquals (\_ ts -> Prelude.foldr f r ts) (\t1 t2 -> f t2 (f t1 r)) pr
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq

instance IsFirstOrder (PropForm MyAtom) MyAtom Predicate MyTerm V Function
instance IsQuantified (PropForm MyAtom) MyAtom V
instance IsPropositional CNF MyAtom
instance IsCombinable CNF
instance HasBoolean CNF
instance IsNegatable CNF
instance HasFixity CNF
instance IsLiteral CNF MyAtom
instance IsFormula CNF MyAtom

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
    | SkolemNumbers (Set Function)
    | ClauseNormalForm (Set (Set formula))
    | TrivialClauses [(Bool, (Set formula))]
    | ConvertToChiou (Ch.Sentence V Predicate Function)
    | ChiouKB1 (Proof formula)
    | PropLogicSat Bool
    | SatSolverCNF CNF
    | SatSolverSat Bool
    -- deriving (Data, Typeable)

-- | Predicate isn't really made to have a HasBoolean instance, but we need one for some tests.
instance HasBoolean Predicate where
    asBool (NamedPredicate s) = readMay s
    fromBool = NamedPredicate . show

deriving instance Show (Ch.Sentence V Predicate Function)
deriving instance Show (Ch.CTerm V Function)

type TTestFormula = TestFormula MyFormula MyAtom V

doTest :: TTestFormula -> Test
doTest (TestFormula formula name expected) =
    TestLabel name $ TestList $
    List.map (doExpected formula name) expected

doExpected formula name expected@(FirstOrderFormula f') = let label = (name ++ " original formula") in TestLabel label (TestCase (assertEqual label f' formula))
doExpected formula name expected@(SimplifiedForm f') = let label = (name ++ " simplified") in TestLabel label (TestCase (assertEqual label f' (simplify formula)))
doExpected formula name expected@(PrenexNormalForm f') = let label = (name ++ " prenex normal form") in TestLabel label (TestCase (assertEqual label f' (pnf formula)))
doExpected formula name expected@(NegationNormalForm f') = let label = (name ++ " negation normal form") in TestLabel label (TestCase (assertEqual label f' (nnf . simplify $ formula)))
doExpected formula name expected@(SkolemNormalForm f') = let label = (name ++ " skolem normal form") in TestLabel label (TestCase (assertEqual label f' (runSkolem (skolemize id formula :: SkolemT Identity MyFormula))))
doExpected formula name expected@(SkolemNumbers f') = let label = (name ++ " skolem numbers") in TestLabel label (TestCase (assertEqual label f' (skolemSet (runSkolem (skolemize id formula :: SkolemT Identity MyFormula)))))
doExpected formula name expected@(ClauseNormalForm fss) =
    let label = (name ++ " clause normal form") in
    TestLabel label (TestCase (assertEqual label
                                           (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (fss :: (Set (Set MyFormula)))))
                                           (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (Set.map (Set.map id) (simpcnf' formula) :: Set (Set MyFormula))))))
doExpected formula name expected@(TrivialClauses flags) = let label = (name ++ " trivial clauses") in TestLabel label (TestCase (assertEqual label flags (List.map (\ (x :: Set MyFormula) -> (trivial x, x)) (Set.toList (simpcnf' (formula :: MyFormula))))))
doExpected formula name expected@(ConvertToChiou result) =
          -- We need to convert formula to Chiou and see if it matches result.
          let ca :: MyAtom -> Ch.Sentence V Predicate Function
              -- ca = undefined
              ca = foldEquals (\p ts -> Ch.Predicate p (List.map ct ts)) (\t1 t2 -> Ch.Equal (ct t1) (ct t2))
              ct :: MyTerm -> Ch.CTerm V Function
              ct = foldTerm cv fn
              cv :: V -> Ch.CTerm V Function
              cv = vt
              fn :: Function -> [MyTerm] -> Ch.CTerm V Function
              fn f ts = fApp f (List.map ct ts) in
          let label = (name ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual label result (convertFirstOrder ca id formula :: Ch.Sentence V Predicate Function)))
doExpected formula name expected@(ChiouKB1 result) = let label = (name ++ " Chiou KB") in TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB [formula] >>= return . head))))
doExpected formula name expected@(PropLogicSat result) = let label = (name ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual label result (runSkolem (plSat (convertFirstOrder id id formula)))))
doExpected formula name expected@(SatSolverCNF result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label (norm result) (runNormal (SS.toCNF formula))))
doExpected formula name expected@(SatSolverSat result) = let label = (name ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label result ((List.null :: [a] -> Bool) (runNormalT (SS.toCNF formula >>= return . satisfiable)))))

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

skolemSet :: forall formula atom term v p f. (IsQuantified formula atom v, HasEquality atom p term, IsTerm term v f, Data formula, Data f, HasSkolem f v) => formula -> Set f
skolemSet =
    Prelude.foldr ins Set.empty . skolemList
    where
      ins :: f -> Set f -> Set f
      ins f s = maybe s (const (Set.insert f s)) (fromSkolem f)
      skolemList :: (IsQuantified formula atom v, HasEquality atom p term, IsTerm term v f, Data f, Typeable f, Data formula) => formula -> [f]
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

type TTestProof = TestProof MyFormula MyTerm V

data ProofExpected formula v term
    = ChiouResult (Bool, SetOfSupport formula v term)
    | ChiouKB (Set (WithId (ImplicativeForm formula)))
    deriving (Data, Typeable)

{-
doProof :: forall formula atom term v p f. (IsQuantified formula atom v,
                                            IsPropositional formula atom,
                                            HasEquality atom p term, atom ~ FOL p (Term v f),
                                            IsTerm term v f, term ~ Term v f,
                                            IsLiteral formula atom,
                                            Ord formula, Data formula, Typeable v, Eq term, Show term, Show v, Show formula, Eq p, Ord f, Show f) =>
           TestProof formula term v -> Test
-}
doProof :: forall formula atom p term v f.
           (IsFirstOrder formula atom p term v f,
            HasEquality atom p term,
            Atom atom term v,
            HasSkolem f v,
            Eq formula, Eq term, Eq v, Ord term, Show formula, Show term, Data formula, Typeable f, Show v) => TestProof formula term v -> Test
doProof p =
    TestLabel (proofName p) $ TestList $
    concatMap doExpected (proofExpected p)
    where
      doExpected :: ProofExpected formula v term -> [Test]
      doExpected (ChiouResult result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " using Chiou prover") in
           TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB' kb >> theoremKB' c))))]
      doExpected (ChiouKB result) =
          [let label = (proofName p ++ " with " ++ fst (proofKnowledge p) ++ " Chiou knowledge base") in
           TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB kb >> getKB))))]
      kb = snd (proofKnowledge p) :: [formula]
      c = conjecture p :: formula

loadKB' :: forall m formula lit atom p term v f.
           (lit ~ formula,
            Monad m, Data formula,
            IsFirstOrder formula atom p term v f,
            IsQuantified formula atom v,
            HasEquality atom p term,
            HasSkolem f v,
            IsLiteral lit atom,
            Atom atom term v,
            IsTerm term v f, Typeable f) => [formula] -> ProverT' v term (ImplicativeForm formula) m [Proof formula]
loadKB' = loadKB

theoremKB' :: forall m formula lit atom p term v f.
              (lit ~ formula,
               Monad m, Data formula,
               IsFirstOrder formula atom p term v f,
               IsQuantified formula atom v,
               HasEquality atom p term,
               HasSkolem f v,
               IsLiteral lit atom,
               Atom atom term v,
               IsTerm term v f, Typeable f) => formula -> ProverT' v term (ImplicativeForm formula) m (Bool, SetOfSupport formula v term)
theoremKB' = theoremKB
