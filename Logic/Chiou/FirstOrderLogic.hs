{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS -Wall -Werror #-}

{- FirstOrderLogic.hs -}
{-
  The syntax of first order logic in BNF is:
  
  Sentence -> AtomicSentence
           |  Sentence Connective
	   |  Quantifier Variable, ... Sentence
	   |  NOT Sentence
	   | (Sentence)
	   
  AtomicSentence -> Predicate(Term, ...)
                 |  Term = Term

  Term -> Function (Term)
       |  Constant
       |  Variable

  Connective -> =>
             |  <=>
             |  AND
	     |  OR

  Quantifier -> ForAll
             |  Exists

  Constant -> A | X | John | ...
  
  Variable -> a | x | s | ...

  Predicate -> Before | HasColor | Raining | ...

  Function -> Mother | LeftLegOf | ...

  [Source: S. Russel, P. Norvig, "Artificial Intelligence: A modern Approach",
           p187]
  -}

module Logic.Chiou.FirstOrderLogic
    ( Sentence(..)
    , Term(..)
    , Connective(..)
    , Quantifier(..)
    ) where

data Sentence v p f
    = Connective (Sentence v p f) Connective (Sentence v p f)
    | Quantifier Quantifier [v] (Sentence v p f)
    | Not (Sentence v p f)
    | Predicate p [Term v f]
    | Equal (Term v f) (Term v f)
    deriving (Eq, Ord)

data Term v f
    = Function f [Term v f]
    | Variable v
    deriving (Eq, Ord)

data Connective
    = Imply
    | Equiv
    | And
    | Or
    deriving (Eq, Ord)

data Quantifier
    = ForAll
    | ExistsCh
    deriving (Eq, Ord)
