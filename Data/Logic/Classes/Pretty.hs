{-# LANGUAGE CPP, FlexibleInstances, TypeSynonymInstances #-}
module Data.Logic.Classes.Pretty
#if 1
    ( module Pretty
    ) where

import Pretty
#else
    ( Logic(Logic, unLogic)
    , Pretty(pPrint)
    , HasFixity(fixity)
    , TH.Fixity(..)
    , TH.FixityDirection(..)
    , topFixity
    , botFixity
    ) where

import Data.Monoid ((<>))
import Data.List as List (intersperse, map)
import Data.Set as Set (Set, toAscList)
import qualified Language.Haskell.TH.Syntax as TH
import Text.PrettyPrint.HughesPJClass (Pretty(pPrint), text)
{-
import Text.PrettyPrint (Doc, text)

-- | The intent of this class is to be similar to Show, but only one
-- way, with no corresponding Read class.  It doesn't really belong
-- here in logic-classes.  To put something in a pretty printing class
-- implies that there is only one way to pretty print it, which is not
-- an assumption made by Text.PrettyPrint.  But in practice this is
-- often good enough.
class Pretty x where
    pretty :: x -> Doc

instance Pretty String where
    pPrint = text
-}

newtype Logic a = Logic {unLogic :: a}

-- | A class used to do proper parenthesization of formulas.  If we
-- nest a higher precedence formula inside a lower one parentheses can
-- be omitted.  Because @|@ has lower precedence than @&@, the formula
-- @a | (b & c)@ appears as @a | b & c@, while @(a | b) & c@ appears
-- unchanged.  (Name Precedence chosen because Fixity was taken.)
-- 
-- The second field of Fixity is the FixityDirection, which can be
-- left, right, or non.  A left associative operator like @/@ is
-- grouped left to right, so parenthese can be omitted from @(a / b) /
-- c@ but not from @a / (b / c)@.  It is a syntax error to omit
-- parentheses when formatting a non-associative operator.
-- 
-- The Haskell FixityDirection type is concerned with how to interpret
-- a formula formatted in a certain way, but here we are concerned
-- with how to format a formula given its interpretation.  As such,
-- one case the Haskell type does not capture is whether the operator
-- follows the associative law, so we can omit parentheses in an
-- expression such as @a & b & c@.
class HasFixity x where
    fixity :: x -> TH.Fixity

-- Definitions from template-haskell:
-- data Fixity = Fixity Int FixityDirection
-- data FixityDirection = InfixL | InfixR | InfixN

-- | This is used as the initial value for the parent fixity.
topFixity :: TH.Fixity
topFixity = TH.Fixity 0 TH.InfixN

-- | This is used as the fixity for things that never need
-- parenthesization, such as function application.
botFixity :: TH.Fixity
botFixity = TH.Fixity 10 TH.InfixN

instance Pretty a => Pretty (Set a) where
    pPrint s = text "{" <> mconcat (intersperse (text ", ") (List.map pPrint (Set.toAscList s))) <> text "}"
#endif
