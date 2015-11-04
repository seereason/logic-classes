module Data.Logic
    ( module Data.Logic.Classes.Atom
    , module Prop
    , module Data.Logic.Normal.Implicative
    , module Data.Logic.Instances.Test
    , module Data.Set
    , module Data.String
    , module Text.PrettyPrint.HughesPJClass
    ) where

import Data.Logic.Classes.Atom
import Prop hiding (Atom, T, F, Not, And, Or, Imp, Iff, nnf)
import Data.Logic.Normal.Implicative
import Data.Logic.Instances.Test hiding (Formula, V, Predicate, Formula, SkTerm, Skolem, SkAtom, Var, Fn)
import Data.Set
import Data.String
import Text.PrettyPrint.HughesPJClass (pPrint, prettyShow)
