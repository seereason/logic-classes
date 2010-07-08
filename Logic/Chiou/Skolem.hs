-- |Assign Skolem numbers to the terms of a formula in implicative
-- normal form.
module Logic.Chiou.Skolem
    ( assignSkolemL
    ) where

import Control.Monad.State (get)
import Logic.Chiou.FirstOrderLogic (Term(..))
import Logic.Chiou.Monad (ProverT, SkolemCount, State(skolemCount))
import Logic.Chiou.NormalForm (ImplicativeNormalForm(..), NormalSentence(..))
import Logic.Predicate (Skolem(..))

assignSkolemL :: (Monad m, Skolem f) => [ImplicativeNormalForm v p f] -> SkolemCount -> ProverT v p f m ([(ImplicativeNormalForm v p f, SkolemCount)], SkolemCount)
assignSkolemL [] _ = return ([], 0)
assignSkolemL (x:xs) i = do (x', n1) <- assignSkolem x i
			    (xs', n2) <- assignSkolemL xs i
			    return (x' ++ xs', max n1 n2)

assignSkolem :: (Monad m, Skolem f) => ImplicativeNormalForm v p f -> SkolemCount -> ProverT v p f m ([(ImplicativeNormalForm v p f, SkolemCount)], SkolemCount)
assignSkolem (INF lhs rhs) i =
    do (lhs', n1) <- assignSkolem' lhs
       (rhs', n2) <- assignSkolem' rhs
       let inf = if n2 > 0 then
	           map (\x -> (x, i)) (splitSkolem (INF lhs' rhs'))
		 else
		   [((INF lhs' rhs'), i)]
       return (inf, max n1 n2)

assignSkolem' :: (Monad m, Skolem f) => [NormalSentence v p f] -> ProverT v p f m ([NormalSentence v p f], SkolemCount)
assignSkolem' [] = return ([], 0)
assignSkolem' (x:xs) = do (x', n1) <- assignSkolem'' x
			  (xs', n2) <- assignSkolem' xs
			  return ((x':xs'), max n1 n2)

assignSkolem'' :: (Monad m, Skolem f) => NormalSentence v p f -> ProverT v p f m (NormalSentence v p f, SkolemCount)
assignSkolem'' (NFNot s) = do (s', n) <- assignSkolem'' s
			      return (NFNot s', n)
assignSkolem'' (NFPredicate p ts) = do (ts', n) <- skSubstituteL ts
				       return (NFPredicate p ts', n)
assignSkolem'' (NFEqual t1 t2) = do (t1', n1) <- skSubstitute t1
				    (t2', n2) <- skSubstitute t2
				    return (NFEqual t1' t2', max n1 n2)

skSubstituteL :: (Monad m, Skolem f) => [Term v f] -> ProverT v p f m ([Term v f], SkolemCount)
skSubstituteL [] = return ([], 0)
skSubstituteL (t:ts) = do (t', n1) <- skSubstitute t
			  (ts', n2) <- skSubstituteL ts
			  return (t':ts', max n1 n2)

{-
skSubstitute :: (Monad m, Enum f) => Term v f -> ProverT v p f m (Term v f, SkolemCount)
skSubstitute t = case t of
	           (Function f ts) ->
		       do (ts', n) <- skSubstituteL ts
			  return (Function f ts', n)
		   (SkolemFunction n ts) ->
		       do (ts', n') <- skSubstituteL ts
                          st <- get
			  return ((Function (toEnum (fromEnum (toEnum n + skolemCount st))) ts'),
				   max (toEnum n) n')
		   (SkolemConstant n) ->
		       do st <- get
			  return (Constant (toEnum (fromEnum (toEnum n + skolemCount st))), toEnum n)
		   _ -> return (t, 0)
-}

skSubstitute :: (Monad m, Skolem f) => Term v f -> ProverT v p f m (Term v f, SkolemCount)
skSubstitute t = case t of
	           (Function f ts) ->
                       case fromSkolem f of
                         Nothing ->
		             do (ts', n) <- skSubstituteL ts
			        return (Function f ts', n)
                         Just n ->
                             do (ts', n') <- skSubstituteL ts
                                st <- get
			        return ((Function (toSkolem (n + skolemCount st)) ts'),
				        max n n')
{-
		   Constant f ->
                       case fromSkolem f of
                         Nothing -> return (t, 0)
                         Just n ->
                             do st <- get
			        return (Constant (toSkolem (n + skolemCount st)), n)
-}
                   Variable _ -> return (t, 0)

splitSkolem :: ImplicativeNormalForm v p f -> [ImplicativeNormalForm v p f]
splitSkolem (INF lhs []) = [INF lhs []]
splitSkolem (INF lhs (x:[])) = [INF lhs [x]]
splitSkolem (INF lhs (x:xs)) = (INF lhs [x]):(splitSkolem (INF lhs xs))
