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
import Data.Boolean (CNF, Literal)
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
import FOL (asubst, convertFirstOrder, fApp, foldEquate, foldTerm, funcs, fva, HasEquate,
            IsFirstOrder, IsQuantified(..), IsTerm, Predicate(NamedPredicate), V, vt)
import Formulas (IsCombinable(..), HasBoolean(fromBool, asBool), IsNegatable(..), IsFormula(..))
import Lit (IsLiteral(..))
import Pretty (Pretty(pPrint), HasFixity(..))
import Prop (IsPropositional(..), PFormula, satisfiable, trivial)
import PropLogic (PropForm)
import Safe (readMay)
import Skolem (Function, MyAtom, MyTerm, SkolemT, MyFormula, MyAtom, MyTerm, simpcnf', HasSkolem)
import Test.HUnit
import Text.PrettyPrint (Style(mode), renderStyle, style, Mode(OneLineMode))

instance Atom MyAtom MyTerm V where
    substitute = asubst
    freeVariables = fva
    allVariables = fva -- Variables are always free in an atom - this method is unnecessary
    unify = unify
    match = unify
    foldTerms f r pr = foldEquate (\_ ts -> Prelude.foldr f r ts) (\t1 t2 -> f t2 (f t1 r)) pr
    isRename = isRenameOfAtomEq
    getSubst = getSubstAtomEq

instance IsFirstOrder (PropForm MyAtom) MyAtom Predicate MyTerm V Function

-- | We shouldn't need this instance, but right now we need ot to use
-- convertFirstOrder.  The conversion functions need work.
instance IsQuantified (PropForm MyAtom) MyAtom V where
    quant _ _ _ = error "FIXME: IsQuantified (PropForm MyAtom) MyAtom V"
    foldQuantified = error "FIXME: IsQuantified (PropForm MyAtom) MyAtom V"

instance IsPropositional CNF MyAtom where
    foldPropositional' = error "FIXME: IsPropositional CNF MyAtom"
instance IsCombinable CNF where
    foldCombination = error "FIXME: IsCombinable CNF"
    _ .|. _ = error "FIXME: IsCombinable CNF"
    _ .&. _ = error "FIXME: IsCombinable CNF"
    _ .=>. _ = error "FIXME: IsCombinable CNF"
    _ .<=>. _ = error "FIXME: IsCombinable CNF"
instance HasBoolean CNF where
    asBool = error "FIXME: HasBoolean CNF"
    fromBool = error "FIXME: HasBoolean CNF"
instance IsNegatable CNF where
    naiveNegate = error "FIXME: IsNegatable CNF"
    foldNegation' = error "FIXME: IsNegatable CNF"
instance HasFixity CNF where
    fixity = error "FIXME: HasFixity CNF"
instance IsLiteral CNF MyAtom where
    foldLiteral = error "FIXME: IsLiteral CNF MyAtom"
instance IsFormula CNF MyAtom where
    atomic = error "FIXME: IsFormula CNF MyAtom"
    overatoms = error "FIXME: IsFormula CNF MyAtom"
    onatoms = error "FIXME: IsFormula CNF MyAtom"

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
    asBool _ = Nothing
    fromBool = NamedPredicate . show

deriving instance Show (Ch.Sentence V Predicate Function)
deriving instance Show (Ch.CTerm V Function)

type TTestFormula = TestFormula MyFormula MyAtom V

doTest :: TTestFormula -> Test
doTest (TestFormula fm nm expect) =
    TestLabel nm $ TestList $
    List.map doExpected expect
    where
      doExpected :: Expected MyFormula MyAtom V -> Test
      doExpected (FirstOrderFormula f') = let label = (nm ++ " original formula") in TestLabel label (TestCase (assertEqual label f' fm))
      doExpected (SimplifiedForm f') = let label = (nm ++ " simplified") in TestLabel label (TestCase (assertEqual label f' (simplify fm)))
      doExpected (PrenexNormalForm f') = let label = (nm ++ " prenex normal form") in TestLabel label (TestCase (assertEqual label f' (pnf fm)))
      doExpected (NegationNormalForm f') = let label = (nm ++ " negation normal form") in TestLabel label (TestCase (assertEqual label f' (nnf . simplify $ fm)))
      doExpected (SkolemNormalForm f') = let label = (nm ++ " skolem normal form") in TestLabel label (TestCase (assertEqual label f' (runSkolem (skolemize id fm :: SkolemT Identity (PFormula MyAtom)))))
      doExpected (SkolemNumbers f') = let label = (nm ++ " skolem numbers") in TestLabel label (TestCase (assertEqual label f' (skolemSet (runSkolem (skolemize id fm :: SkolemT Identity (PFormula MyAtom))))))
      doExpected (ClauseNormalForm fss) =
          let label = (nm ++ " clause normal form") in
          TestLabel label (TestCase (assertEqual label
                                                 (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (fss :: (Set (Set MyFormula)))))
                                                 (show (List.map (List.map pPrint) . Set.toList . Set.map Set.toList $ (Set.map (Set.map id) (simpcnf' fm) :: Set (Set MyFormula))))))
      doExpected (TrivialClauses flags) = let label = (nm ++ " trivial clauses") in TestLabel label (TestCase (assertEqual label flags (List.map (\ (x :: Set MyFormula) -> (trivial x, x)) (Set.toList (simpcnf' (fm :: MyFormula))))))
      doExpected (ConvertToChiou result) =
                -- We need to convert formula to Chiou and see if it matches result.
                let ca :: MyAtom -> Ch.Sentence V Predicate Function
                    -- ca = undefined
                    ca = foldEquate (\p ts -> Ch.Predicate p (List.map ct ts)) (\t1 t2 -> Ch.Equal (ct t1) (ct t2))
                    ct :: MyTerm -> Ch.CTerm V Function
                    ct = foldTerm cv fn
                    cv :: V -> Ch.CTerm V Function
                    cv = vt
                    fn :: Function -> [MyTerm] -> Ch.CTerm V Function
                    fn f ts = fApp f (List.map ct ts) in
                let label = (nm ++ " converted to Chiou") in TestLabel label (TestCase (assertEqual label result (convertFirstOrder ca id fm :: Ch.Sentence V Predicate Function)))
      doExpected (ChiouKB1 result) = let label = (nm ++ " Chiou KB") in TestLabel label (TestCase (assertEqual label result (runProver' Nothing (loadKB [fm] >>= return . head))))
      doExpected (PropLogicSat result) = let label = (nm ++ " PropLogic.satisfiable") in TestLabel label (TestCase (assertEqual label result (runSkolem (plSat (convertFirstOrder id id fm)))))
      doExpected (SatSolverCNF result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label (norm result) (runNormal (SS.toCNF fm))))
      doExpected (SatSolverSat result) = let label = (nm ++ " SatSolver CNF") in TestLabel label (TestCase (assertEqual label result ((List.null :: [a] -> Bool) (runNormalT (SS.toCNF fm >>= return . satisfiable)))))

-- p = id

norm :: [[Literal]] -> [[Literal]]
norm = List.map Set.toList . Set.toList . Set.fromList . List.map Set.fromList

skolemSet :: PFormula MyAtom -> Set Function
skolemSet = Set.map fst . funcs

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
                                            HasEquate atom p term, atom ~ FOL p (Term v f),
                                            IsTerm term v f, term ~ Term v f,
                                            IsLiteral formula atom,
                                            Ord formula, Data formula, Typeable v, Eq term, Show term, Show v, Show formula, Eq p, Ord f, Show f) =>
           TestProof formula term v -> Test
-}
doProof :: forall formula atom p term v f.
           (IsFirstOrder formula atom p term v f,
            HasEquate atom p term,
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
            HasEquate atom p term,
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
               HasEquate atom p term,
               HasSkolem f v,
               IsLiteral lit atom,
               Atom atom term v,
               IsTerm term v f, Typeable f) => formula -> ProverT' v term (ImplicativeForm formula) m (Bool, SetOfSupport formula v term)
theoremKB' = theoremKB
