-- |
-- Module     : Unbound.Generics.LocallyNameless.Internal.Fold
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- | Some utilities for working with Folds.
{-# LANGUAGE RankNTypes #-}
module Unbound.Generics.LocallyNameless.Internal.Fold (Fold, Traversal', toListOf, filtered, justFiltered) where

import Control.Applicative
import Data.Maybe (fromJust)
import Data.Functor.Contravariant
import Data.Monoid

type Getting r s a = (a -> Const r a) -> s -> Const r s

type Fold s a = forall f . (Contravariant f, Applicative f) => (a -> f a) -> s -> f s

type Traversal' s a = forall f . Applicative f => (a -> f a) -> s -> f s

toListOf :: Fold s a -> s -> [a]
-- toListOf :: Getting (Endo [a]) s a -> s -> [a]
toListOf l = foldrOf l (:) []
{-# INLINE toListOf #-}

foldMapOf :: Getting r s a -> (a -> r) -> s -> r
foldMapOf l f = getConst . l (Const . f)
{-# INLINE foldMapOf #-}

foldrOf :: Getting (Endo r) s a -> (a -> r -> r) -> r -> s -> r
foldrOf l f z = fmap (flip appEndo z) (foldMapOf l (Endo .f))
{-# INLINE foldrOf #-}

filtered :: (a -> Bool) -> Traversal' a a
filtered p afa x = if p x then afa x else pure x
{-# INLINE filtered #-}

justFiltered :: (a -> Maybe b) -> Fold a b
justFiltered p bfb x = case p x of
                        Just b -> contramap (fromJust . p) (bfb b)
                        Nothing -> pure x
{-# INLINE justFiltered #-}
