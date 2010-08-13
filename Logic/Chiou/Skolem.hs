{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS -Wwarn #-}
-- |Assign Skolem numbers to the terms of a formula in implicative
-- normal form.
module Logic.Chiou.Skolem
    ( assignSkolemL
    ) where

--import Debug.Trace
import Control.Monad.State (get)
import Logic.Chiou.FirstOrderLogic (Term(..))
import Logic.Chiou.Monad (ProverT, SkolemCount, ProverState(skolemOffset, sentenceCount), WithId(..), withId)
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..))
import Logic.FirstOrder (Skolem(..))

collect :: ([a] -> c) -> ([b] -> d) -> [(a, b)] -> (c, d)
collect fx fy pairs = let (xs, ys) = unzip pairs in (fx xs, fy ys)

-- |This function is used to change the skolem number of a collection
-- of formulas so they are all non-overlapping.  Add the offset i to
-- the skolem numbers in the formula, returning the resulting formula
-- and the number of the highest skolem number encountered.
assignSkolemL :: forall m v p f. (Monad m, Skolem f) => [ImplicativeNormalForm v p f] -> ProverT v p f m ([WithId (ImplicativeNormalForm v p f)], SkolemCount)
assignSkolemL xs = mapM assignSkolem xs >>= return . collect concat (foldr max 0)

assignSkolem :: (Monad m, Skolem f) => ImplicativeNormalForm v p f -> ProverT v p f m ([WithId (ImplicativeNormalForm v p f)], SkolemCount)
assignSkolem (INF lhs rhs) =
    do i <- get >>= return . sentenceCount
       (lhs', n1) <- assignSkolem' lhs
       (rhs', n2) <- assignSkolem' rhs
       return (map (withId i) [INF lhs' rhs'], max n1 n2)

assignSkolem' :: (Monad m, Skolem f) => [NormalSentence v p f] -> ProverT v p f m ([NormalSentence v p f], SkolemCount)
assignSkolem' xs = mapM assignSkolem'' xs >>= return . collect id (foldr max 0)

assignSkolem'' :: (Monad m, Skolem f) => NormalSentence v p f -> ProverT v p f m (NormalSentence v p f, SkolemCount)
assignSkolem'' (NFNot s) =
    assignSkolem'' s >>= \ (s', n) -> return (NFNot s', n)
assignSkolem'' (NFPredicate p ts) =
    skSubstituteL ts >>= \ (ts', n) -> return (NFPredicate p ts', n)
assignSkolem'' (NFEqual t1 t2) =
    skSubstitute t1 >>= \ (t1', n1) ->
    skSubstitute t2 >>= \ (t2', n2) ->
    return (NFEqual t1' t2', max n1 n2)

skSubstituteL :: (Monad m, Skolem f) => [Term v f] -> ProverT v p f m ([Term v f], SkolemCount)
skSubstituteL ts = mapM skSubstitute ts >>= return . collect id (foldr max 0)

skSubstitute :: (Monad m, Skolem f) => Term v f -> ProverT v p f m (Term v f, SkolemCount)
skSubstitute t = case t of
	           (Function f ts) ->
                       case fromSkolem f of
                         Nothing ->
		             do (ts', n) <- skSubstituteL ts
			        return (Function f ts', n)
                         Just n ->
                             do (ts', n') <- skSubstituteL ts
                                offset <- get >>= return . skolemOffset
			        return ((Function (toSkolem (n + offset)) ts'), max n n')
                   Variable _ -> return (t, 0)
