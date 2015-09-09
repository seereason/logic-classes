{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
module Data.Logic.Harrison.DefCNF
    {- ( Atom
    , NumAtom(ma, ai)
    , defcnfs
    , defcnf1
    , defcnf
    , defcnf3
    ) -} where

import Data.Logic.Classes.Combine (Combination(..), BinOp(..), (.&.), (.|.), (.<=>.))
import Data.Logic.Classes.Formula (Formula(atomic))
import Data.Logic.Classes.Literal (Literal)
import Data.Logic.Classes.Negate ((.~.))
import Data.Logic.Classes.Pretty
import Data.Logic.Classes.Propositional (PropositionalFormula(foldPropositional), overatoms)
import Data.Logic.Harrison.Prop (nenf, simpcnf, cnf, cnf')
import qualified Data.Logic.Types.Propositional as P
-- import Data.Logic.Types.Harrison.Prop (Prop(P))
import qualified Data.Map as Map
import Data.Set.Extra as Set
import Test.HUnit
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), prettyShow, text)

data Atom = P String Integer deriving (Eq, Ord, Show)

instance Pretty Atom where
    pPrint (P s n) = text (s ++ if n == 0 then "" else show n)

class NumAtom atom where
    ma :: Integer -> atom
    ai :: atom -> Integer

instance NumAtom Atom where
    ma = P "p_"
    ai (P _ n) = n

instance HasFixity Atom where
    fixity _ = botFixity

-- ========================================================================= 
-- Definitional CNF.                                                         
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 

test01 :: Test
test01 =
    let ((p, q, r) :: (P.Formula Atom, P.Formula Atom, P.Formula Atom)) =
                      (atomic (P "p" 0), atomic (P "q" 0), atomic (P "r" 0)) in
    TestCase $ assertEqual "cnf <<p <=> (q <=> r)>>"
                           "(¬r ∨ p ∨ ¬q) ∧ (¬r ∨ q ∨ ¬p) ∧ (q ∨ r ∨ p) ∧ (¬q ∨ r ∨ ¬p)"
                           (prettyShow (cnf' (p .<=>. (q .<=>. r))))

-- ------------------------------------------------------------------------- 
-- Make a stylized variable and update the index.                            
-- ------------------------------------------------------------------------- 

mkprop :: forall pf atom. (PropositionalFormula pf atom, NumAtom atom) => Integer -> (pf, Integer)
mkprop n = (atomic (ma n :: atom), n + 1)

-- ------------------------------------------------------------------------- 
-- Core definitional CNF procedure.                                          
-- ------------------------------------------------------------------------- 

maincnf :: (NumAtom atom, PropositionalFormula pf atom) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
maincnf trip@(fm, _defs, _n) =
    foldPropositional co tf at fm
    where
      co (BinOp p (:&:) q) = defstep (.&.) (p,q) trip
      co (BinOp p (:|:) q) = defstep (.|.) (p,q) trip
      co (BinOp p (:<=>:) q) = defstep (.<=>.) (p,q) trip
      co (BinOp _ (:=>:) _) = trip
      co ((:~:) _) = trip
      tf _ = trip
      at _ = trip

defstep :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf -> pf -> pf) -> (pf, pf) -> (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
defstep op (p,q) (_fm, defs, n) =
  let (fm1,defs1,n1) = maincnf (p,defs,n) in
  let (fm2,defs2,n2) = maincnf (q,defs1,n1) in
  let fm' = op fm1 fm2 in
  case Map.lookup fm' defs2 of
    Just _ -> (fm', defs2, n2)
    Nothing -> let (v,n3) = mkprop n2 in (v, Map.insert v (v .<=>. fm') defs2,n3)

-- ------------------------------------------------------------------------- 
-- Make n large enough that "v_m" won't clash with s for any m >= n          
-- ------------------------------------------------------------------------- 

max_varindex :: NumAtom atom =>  atom -> Integer -> Integer
max_varindex atom n = max n (ai atom)

-- ------------------------------------------------------------------------- 
-- Overall definitional CNF.                                                 
-- ------------------------------------------------------------------------- 

mk_defcnf :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) =>
             ((pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)) -> pf -> Set.Set (Set.Set lit)
mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist {- :: [pf]-}) = Map.elems defs in
  Set.unions (simpcnf fm'' : Prelude.map simpcnf deflist)

defcnf1 :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf1 _ _ fm = cnf (mk_defcnf maincnf fm :: Set.Set (Set.Set lit))


-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 
test02 :: Test
test02 =
    let ((p, q, r, s) :: (P.Formula Atom, P.Formula Atom, P.Formula Atom, P.Formula Atom)) =
            (atomic (P "p" 0), atomic (P "q" 0), atomic (P "r" 0), atomic (P "s" 0))
        fm :: P.Formula Atom
        fm = (p .|. (q .&. ((.~.)r))) .&. s in
    TestCase $ assertEqual "defcnf1 (p | (q & ~r)) & s"
                           (unlines ["(¬s ∨ p_3 ∨ ¬p_2) ∧ ",
                                     "(p ∨ p_1 ∨ ¬p_2) ∧ ",
                                     "(p_1 ∨ r ∨ ¬q) ∧ ",
                                     "(p_2 ∨ ¬p) ∧ ",
                                     "(p_2 ∨ ¬p_1) ∧ ",
                                     "(p_2 ∨ ¬p_3) ∧ ",
                                     "(q ∨ ¬p_1) ∧ ",
                                     "(s ∨ ¬p_3) ∧ ",
                                     "p_3 ∧ ",
                                     "(¬r ∨ ¬p_1)"])
                           (prettyShow ((defcnf1 (undefined :: P.Formula Atom) (undefined :: Atom) fm :: P.Formula Atom)))

-- ------------------------------------------------------------------------- 
-- Version tweaked to exploit initial structure.                             
-- ------------------------------------------------------------------------- 

subcnf :: (PropositionalFormula pf atom, NumAtom atom) =>
          ((pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer))
       -> (pf -> pf -> pf)
       -> pf
       -> pf
       -> (pf, Map.Map pf pf, Integer)
       -> (pf, Map.Map pf pf, Integer)
subcnf sfn op p q (_fm,defs,n) =
  let (fm1,defs1,n1) = sfn (p,defs,n) in
  let (fm2,defs2,n2) = sfn (q,defs1,n1) in
  (op fm1 fm2, defs2, n2)

orcnf :: (NumAtom atom, PropositionalFormula pf atom) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:|:) q) = subcnf orcnf (.|.) p q trip
      co _ = maincnf trip

andcnf :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf (.&.) p q trip
      co _ = orcnf trip

defcnfs :: (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => pf -> Set.Set (Set.Set lit)
defcnfs fm = mk_defcnf andcnf fm

defcnf :: forall pf lit atom.(PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf _ _ fm = cnf (defcnfs fm :: Set.Set (Set.Set lit))

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 
test03 :: Test
test03 =
    let ((p, q, r, s) :: (P.Formula Atom, P.Formula Atom, P.Formula Atom, P.Formula Atom)) =
            (atomic (P "p" 0), atomic (P "q" 0), atomic (P "r" 0), atomic (P "s" 0))
        fm :: P.Formula Atom
        fm = (p .|. (q .&. ((.~.)r))) .&. s in
    TestCase $ assertEqual "defcnf (p | (q & ~r)) & s (p. 78)"
                           (unlines ["(p_1 ∨ r ∨ ¬q) ∧ ",
                                     "(p_1 ∨ p) ∧ ",
                                     "(q ∨ ¬p_1) ∧ ",
                                     "s ∧ ",
                                     "(¬r ∨ ¬p_1)"])
                           (prettyShow ((defcnf (undefined :: P.Formula Atom) (undefined :: Atom) fm :: P.Formula Atom)))
-- ------------------------------------------------------------------------- 
-- Version that guarantees 3-CNF.                                            
-- ------------------------------------------------------------------------- 

andcnf3 :: (PropositionalFormula pf atom, NumAtom atom, Ord pf) => (pf, Map.Map pf pf, Integer) -> (pf, Map.Map pf pf, Integer)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf3 (.&.) p q trip
      co _ = maincnf trip

defcnf3 :: forall pf lit atom. (PropositionalFormula pf atom, Literal lit atom, NumAtom atom, Ord lit) => lit -> atom -> pf -> pf
defcnf3 _ _ fm = cnf (mk_defcnf andcnf3 fm :: Set.Set (Set.Set lit))

tests = TestList [test01, test02, test03]
