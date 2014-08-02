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
  -- * Implementation details
  , AlphaCtx
  ) where

import Data.Function (on)
import GHC.Generics

import Unbound.Generics.LocallyNameless.Name

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
newtype AlphaCtx = AlphaCtx ()


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
  isPat :: a -> Maybe [AnyName]
  default isPat :: (Generic a, GAlpha (Rep a)) => a -> Maybe [AnyName]
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

  gisPat :: f a -> Maybe [AnyName]

