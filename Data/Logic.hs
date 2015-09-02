module Data.Logic
    ( module Data.Logic.Types.FirstOrder
    -- , module Data.Logic.Types.FirstOrderPublic
    -- , module Data.Logic.Types.Propositional
    , module Data.Logic.Classes.Arity
    , module Data.Logic.Classes.Atom
    , module Data.Logic.Classes.Combine
    , module Data.Logic.Classes.Constants
    , module Data.Logic.Classes.Equals
    , module Data.Logic.Classes.FirstOrder
    , module Data.Logic.Classes.Literal
    , module Data.Logic.Classes.Negate
    , module Data.Logic.Classes.Pretty
    , module Data.Logic.Classes.Propositional
    , module Data.Logic.Classes.Skolem
    , module Data.Logic.Classes.Term
    , module Data.Logic.Classes.Variable
    , module Data.Logic.Normal.Clause
    , module Data.Logic.Normal.Implicative
    -- , module Data.Boolean.SatSolver
    , module Data.Logic.Instances.Test
    , module Data.Set
    , module Data.String
    , module Text.PrettyPrint.HughesPJClass
    ) where

import Data.Logic.Types.FirstOrder
-- import Data.Logic.Types.FirstOrderPublic
-- import Data.Logic.Types.Propositional
import Data.Logic.Classes.Arity
import Data.Logic.Classes.Atom
import Data.Logic.Classes.Combine
import Data.Logic.Classes.Constants
import Data.Logic.Classes.Equals
import Data.Logic.Classes.FirstOrder
import Data.Logic.Classes.Literal hiding (toPropositional)
import Data.Logic.Classes.Negate
import Data.Logic.Classes.Pretty
import Data.Logic.Classes.Propositional hiding (overatoms, clauseNormalForm)
import Data.Logic.Classes.Skolem
import Data.Logic.Classes.Term
import Data.Logic.Classes.Variable
import Data.Logic.Normal.Clause
import Data.Logic.Normal.Implicative
import Data.Logic.Instances.Test
import Data.Set
import Data.String
import Text.PrettyPrint.HughesPJClass (pPrint, prettyShow)

-- > putStrLn (prettyShow ([vt ((fromString ("z"))) .=. fApp ((toSkolem (fromString "y"))) [vt ((fromString ("z")))],(.~.) (vt ((fromString ("x"))) .=. vt ((fromString ("x"))))] :: [TFormula]))
-- [z = sKy[z], ¬x = x]
