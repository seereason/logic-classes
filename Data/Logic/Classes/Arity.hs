module Data.Logic.Classes.Arity
    ( Arity(arity)
    ) where

-- |A class that characterizes how many arguments a predicate or
-- function takes.  Depending on the context, a result of Nothing may
-- mean that the arity is undetermined or unknown, or that any number
-- of arguments may be passed.
class Arity p where
    arity :: p -> Maybe Int
