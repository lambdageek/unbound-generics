{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Alpha
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Use the 'Alpha' typeclass to mark types that may contain 'Name's.
{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}
module Unbound.Generics.LocallyNameless.Alpha (
  -- * Name-aware opertions
  Alpha(..)
  -- * Binder variables
  , DisjointSet(..)
  , inconsistentDisjointSet
  , isConsistentDisjointSet
  -- * Implementation details
  , AlphaCtx
  ) where

import Data.Function (on)
import Data.Foldable (Foldable(..))
import Data.List (intersect)
import Data.Monoid (Monoid(..), (<>))
import GHC.Generics

import Unbound.Generics.LocallyNameless.Name

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
newtype AlphaCtx = AlphaCtx ()

-- | A @DisjointSet a@ is a 'Just' a list of distinct @a@s.  In addition to a monoidal
-- structure, a disjoint set also has an annihilator 'inconsistentDisjointSet'.
--
-- @@
--   inconsistentDisjointSet <> s == inconsistentDisjointSet
--   s <> inconsistentDisjoinSet == inconsistentDisjointSet
-- @@
newtype DisjointSet a = DisjointSet (Maybe [a])

instance Eq a => Monoid (DisjointSet a) where
  mempty = DisjointSet (Just [])
  mappend s1 s2 =
    case (s1, s2) of
      (DisjointSet (Just xs), DisjointSet (Just ys)) | disjointLists xs ys -> DisjointSet (Just (xs <> ys))
      _ -> inconsistentDisjointSet

instance Foldable DisjointSet where
  foldMap summarize (DisjointSet ms) = foldMap (foldMap summarize) ms

inconsistentDisjointSet :: DisjointSet a
inconsistentDisjointSet = DisjointSet Nothing

disjointLists :: Eq a => [a] -> [a] -> Bool
disjointLists xs ys = null (intersect xs ys)

isConsistentDisjointSet :: DisjointSet a -> Bool
isConsistentDisjointSet (DisjointSet Nothing) = False
isConsistentDisjointSet _ = True

-- | Types that are instances of @Alpha@ may participate in name representation.
--
-- Minimal instance is entirely empty, provided that your type is an instance of
-- 'Generic'.
class (Show a) => Alpha a where
  -- | See 'aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = (gaeq c) `on` from

  close :: Alpha b => AlphaCtx -> b -> a -> a
  default close :: (Generic a, GAlpha (Rep a), Alpha b) => AlphaCtx -> b -> a -> a
  close c b = to . gclose c b . from

  open :: Alpha b => AlphaCtx -> b -> a -> a
  default open :: (Generic a, GAlpha (Rep a), Alpha b) => AlphaCtx -> b -> a -> a
  open c b = to . gopen c b . from

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid pattern.
  isPat :: a -> DisjointSet AnyName
  default isPat :: (Generic a, GAlpha (Rep a)) => a -> DisjointSet AnyName
  isPat = gisPat . from
  
  -- | @isEmbed@ is needed internally for the implementation of
  --   'isPat'.  @isEmbed@ is true for terms wrapped in 'Embed' and zero
  --   or more occurrences of 'Shift'.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False

class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool
  gclose :: Alpha b => AlphaCtx -> b -> f a -> f a
  gopen :: Alpha b => AlphaCtx -> b -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName

