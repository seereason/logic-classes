{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module Data.Logic.Harrison.DefCNF
    ( Atom
    , defcnfs
    , defcnf1
    , defcnf2
    , defcnf3
    ) where

import Data.Logic.Classes.Combine (Combination(..), BinOp(..), (.&.), (.|.), (.<=>.))
import Data.Logic.Classes.Propositional (PropositionalFormula(foldPropositional, atomic), overatoms)
import Data.Logic.Harrison.FOL (list_conj, list_disj)
import Data.Logic.Harrison.Prop (nenf, simpcnf)
import qualified Data.Map as Map
import qualified Data.Set.Extra as Set

-- ========================================================================= 
-- Definitional CNF.                                                         
--                                                                           
-- Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  
-- ========================================================================= 
{-
START_INTERACTIVE;;
cnf <<p <=> (q <=> r)>>;;
END_INTERACTIVE;;
-}
-- ------------------------------------------------------------------------- 
-- Make a stylized variable and update the index.                            
-- ------------------------------------------------------------------------- 

data Atom = P Int

mkprop :: (PropositionalFormula pf Atom) => Int -> (pf, Int)
mkprop n = (atomic (P n), n + 1)

-- ------------------------------------------------------------------------- 
-- Core definitional CNF procedure.                                          
-- ------------------------------------------------------------------------- 

maincnf :: (PropositionalFormula pf Atom, Ord pf) => (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
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

defstep :: (PropositionalFormula pf Atom, Ord pf) => (pf -> pf -> pf) -> (pf, pf) -> (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
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

max_varindex :: Atom -> Int -> Int
max_varindex (P m) n = max n m

-- ------------------------------------------------------------------------- 
-- Overall definitional CNF.                                                 
-- ------------------------------------------------------------------------- 

mk_defcnf :: forall pf. (PropositionalFormula pf Atom, Eq pf, Ord pf) =>
             ((pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int))
          -> pf -> Set.Set (Set.Set pf)
mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = 1 + overatoms max_varindex fm' 0 in
  let (fm'',defs,_) = fn (fm',Map.empty,n) in
  let (deflist :: [pf]) = Map.elems defs in
  Set.unions (simpcnf fm'' : map simpcnf deflist)

defcnf1 :: (PropositionalFormula pf Atom, Ord pf) => pf -> pf
defcnf1 fm = list_conj (Set.map list_disj (mk_defcnf maincnf fm))


-- ------------------------------------------------------------------------- 
-- Example.                                                                  
-- ------------------------------------------------------------------------- 
{-
START_INTERACTIVE;;
defcnf1 <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}
-- ------------------------------------------------------------------------- 
-- Version tweaked to exploit initial structure.                             
-- ------------------------------------------------------------------------- 

subcnf :: (PropositionalFormula pf Atom) =>
          ((pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int))
       -> (pf -> pf -> pf)
       -> pf
       -> pf
       -> (pf, Map.Map pf pf, Int)
       -> (pf, Map.Map pf pf, Int)
subcnf sfn op p q (_fm,defs,n) =
  let (fm1,defs1,n1) = sfn (p,defs,n) in
  let (fm2,defs2,n2) = sfn (q,defs1,n1) in
  (op fm1 fm2, defs2, n2)

orcnf :: (PropositionalFormula pf Atom, Ord pf) =>
         (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
orcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:|:) q) = subcnf orcnf (.|.) p q trip
      co _ = maincnf trip

andcnf :: (PropositionalFormula pf Atom, Ord pf) =>
          (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
andcnf trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> orcnf trip) (\ _ -> orcnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf (.&.) p q trip
      co _ = orcnf trip

defcnfs :: (PropositionalFormula pf Atom, Ord pf) => pf -> Set.Set (Set.Set pf)
defcnfs fm = mk_defcnf andcnf fm

defcnf2 :: (PropositionalFormula pf Atom, Ord pf) => pf -> pf
defcnf2 fm = list_conj (Set.map list_disj (defcnfs fm))

-- ------------------------------------------------------------------------- 
-- Examples.                                                                 
-- ------------------------------------------------------------------------- 
{-
START_INTERACTIVE;;
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;
-}
-- ------------------------------------------------------------------------- 
-- Version that guarantees 3-CNF.                                            
-- ------------------------------------------------------------------------- 

andcnf3 :: (PropositionalFormula pf Atom, Ord pf) =>
           (pf, Map.Map pf pf, Int) -> (pf, Map.Map pf pf, Int)
andcnf3 trip@(fm,_defs,_n) =
    foldPropositional co (\ _ -> maincnf trip) (\ _ -> maincnf trip) fm
    where
      co (BinOp p (:&:) q) = subcnf andcnf3 (.&.) p q trip
      co _ = maincnf trip

defcnf3 :: (PropositionalFormula pf Atom, Ord pf) => pf -> pf
defcnf3 fm = list_conj (Set.map list_disj (mk_defcnf andcnf3 fm))
