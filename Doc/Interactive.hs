{-# LANGUAGE FlexibleInstances #-}
-- | Debugging experiments.
import Data.Logic.Classes.Atom
import Data.Logic.Classes.Equals
import Data.Logic.Classes.FirstOrder (prettyFirstOrder)
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Pretty
import Data.Logic.Harrison.Equal
import Data.Logic.Harrison.FOL
import Data.Logic.Harrison.Normal
import Data.Logic.Harrison.Skolem
import Data.Logic.Tests.Harrison.Equal
import Data.Logic.Tests.Common
import Data.Logic.Tests.Harrison.Resolution
import Data.Logic.Types.Harrison.Equal
import Data.Logic.Types.Harrison.Formulas.FirstOrder
import Data.Logic.Harrison.Equal
import qualified Data.Set.Extra as Set
import Text.PrettyPrint (text, (<>))

instance Pretty Int where
    pretty = text . show

instance (Pretty a, Pretty b) => Pretty (a, b) where
    pretty (a, b) = text "(" <> pretty a <> text ", " <> pretty b <> text ")"

main =
    do putStrLn "wishnu:"
       mapM (putStrLn . show . pretty) (Set.toList (functions funcsAtomEq (wishnu :: Formula FOLEQ)))
       putStrLn "equivalence_axioms:"
       mapM (putStrLn . show . pretty) (Set.toList (equivalence_axioms :: Set.Set (Formula FOLEQ)))
       putStrLn "predicates:"
       mapM (putStrLn . show . pretty) (Set.toList (predicates wishnu :: Set.Set (PredicateName PredName)))
       putStrLn "predicate_congruence:"
       mapM (putStrLn . show . pretty) (Set.toList (Set.fold (Set.union . predicate_congruence) (equivalence_axioms :: Set.Set (Formula FOLEQ)) (predicates wishnu :: Set.Set (PredicateName PredName))))
       putStrLn "function_congruence:"
       mapM (putStrLn . show . pretty) (Set.toList (Set.fold (Set.union . function_congruence) (Set.fold (Set.union . predicate_congruence) (equivalence_axioms :: Set.Set (Formula FOLEQ)) (predicates wishnu :: Set.Set (PredicateName PredName))) (functions funcsAtomEq wishnu)))
       putStrLn "equalitize:"
       putStrLn . render $ equalitize (wishnu :: Formula FOLEQ)
       let input = (∀) "y" "g(y)" ⇒ "f(y)"
           expected = (∀) "y" ("g(y)" ⇒ "f(y)")
       putStrLn $ "input: " ++ input ++ "\nexpected: " ++ expected

       putStrLn "puremeson input:"
       mapM (putStrLn . render) . Set.toList $ (Set.map list_conj (simpdnf (runSkolem (askolemize ((.~.) (generalize dpExampleFm))))) :: Set.Set (Formula FOLEQ))

(∀) :: String -> String -> String
(∀) v fm = "for_all (" ++ v ++ ") (" ++ fm ++ ")"

(⇒) :: String -> String -> String
(⇒) l r = "(" ++ l ++ ") ⇒ (" ++ r ++ ")"

infixr 1 ∀
infixr 2 ⇒
