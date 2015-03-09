-- |
-- Module     : Unbound.Generics.LocallyNameless.Name
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Names stand for values.  They may be bound or free.
{-# LANGUAGE DeriveDataTypeable
             , DeriveGeneric
             , ExistentialQuantification
             , FlexibleContexts
             , GADTs #-}
module Unbound.Generics.LocallyNameless.Name
       (
         -- * Names over terms
         Name(..)
       , isFreeName
         -- * Name construction
       , string2Name
       , s2n
       , makeName
         -- * Name inspection
       , name2String
         -- * Heterogeneous names
       , AnyName(..)
       ) where

import Data.Typeable (Typeable, gcast, typeOf)
import GHC.Generics (Generic)

-- | An abstract datatype of names @Name a@ that stand for terms of
-- type @a@.  The type @a@ is used as a tag to distinguish these names
-- from names that may stand for other sorts of terms.
--
-- Two names in a term are consider
-- 'Unbound.Generics.LocallyNameless.Operations.aeq' equal when they
-- are the same name (in the sense of '(==)').  In patterns, however,
-- any two names are equal if they occur in the same place within the
-- pattern.  This induces alpha equivalence on terms in general.
--
-- Names may either be free or bound (see 'isFreeName').  Free names
-- may be extracted from patterns using
-- 'Unbound.Generics.LocallyNameless.Alpha.isPat'.  Bound names
-- cannot be.
-- 
data Name a = Fn String !Integer    -- free names
            | Bn !Integer !Integer  -- bound names / binding level + pattern index
            deriving (Eq, Ord, Typeable, Generic)

-- | Returns 'True' iff the given @Name a@ is free.
isFreeName :: Name a -> Bool
isFreeName (Fn _ _) = True
isFreeName _ = False

-- | Make a free 'Name a' from a 'String'
string2Name :: String -> Name a
string2Name s = makeName s 0

-- | Synonym for 'string2Name'.
s2n :: String -> Name a
s2n = string2Name

-- | Make a name from a 'String' and an 'Integer' index
makeName :: String -> Integer -> Name a
makeName = Fn

-- | Get the integer part of a 'Name'.
name2Integer :: Name a -> String
name2Integer (Fn _ i) = i
name2Integer (Bn _ _) = error "Internal Error: cannot call name2Integer for bound names"

-- | Get the string part of a 'Name'.
name2String :: Name a -> String
name2String (Fn s _) = s
name2String (Bn _ _) = error "Internal Error: cannot call name2String for bound names"

instance Show (Name a) where
  show (Fn "" n) = "_" ++ (show n)
  show (Fn x 0) = x
  show (Fn x n) = x ++ (show n)
  show (Bn x y) = show x ++ "@" ++ show y

-- | An @AnyName@ is a name that stands for a term of some (existentially hidden) type.
data AnyName where
  AnyName :: Typeable a => Name a -> AnyName

instance Show AnyName where
  show (AnyName nm) = show nm

instance Eq AnyName where
  (AnyName n1) == (AnyName n2) = case gcast n2 of
    Just n2' -> n1 == n2'
    Nothing -> False

instance Ord AnyName where
  compare (AnyName n1) (AnyName n2) = case compare (typeOf n1) (typeOf n2) of
    EQ -> case gcast n2 of
      Just n2' -> compare n1 n2'
      Nothing -> error "Equal type representations, but gcast failed in comparing two AnyName values"
    ord -> ord
