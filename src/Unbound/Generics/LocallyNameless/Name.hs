-- |
-- Module: Unbound.Generics.LocallyNameless.Name
-- Copyright: (c) 2014, Aleksey Kliger
-- License: BSD3 (See LICENSE)
--
{-# LANGUAGE DeriveDataTypeable
             , ExistentialQuantification
             , FlexibleContexts
             , GADTs #-}
module Unbound.Generics.LocallyNameless.Name
       (
         Name
       , AnyName(..)
       ) where

import Data.Typeable (Typeable(..), gcast, typeOf)

-- | An abstract datatype of names @Name a@ that stand for values of type @a@.
data Name a = Fn String !Integer    -- free names
            | Bn !Integer !Integer  -- bound names / binding level + pattern index
            deriving (Eq, Ord, Typeable)

-- | An @AnyName@ is a name that stands for a value of some (existentially hidden) type.
data AnyName where
  AnyName :: Typeable a => Name a -> AnyName

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
