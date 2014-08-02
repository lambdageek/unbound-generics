{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Bind
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The fundamental binding form.  The type @'Bind' p t@ allows you to
-- place a pattern @p@ in a term @t@ such that the names in the
-- pattern scope over the term.  Use 'Unbound.Generics.LocallyNameless.Operations.bind'
-- and 'Unbound.Generics.LocallyNameless.Operations.unbind' and 'Unbound.Generics.LocallyNameless.Operations.lunbind'
-- to work with @'Bind' p t@
module Unbound.Generics.LocallyNameless.Bind (
  -- * Name binding
  Bind(..)
  ) where

import Data.Monoid ((<>))

import Unbound.Generics.LocallyNameless.Alpha

data Bind p t = B p t

instance (Show p, Show t) => Show (Bind p t) where
  showsPrec prec (B p t) =
    showParen (prec > 0) (showString "<"
                          . showsPrec prec p
                          . showString "> "
                          . showsPrec 0 t)

instance (Alpha p, Alpha t) => Alpha (Bind p t) where

  aeq' ctx (B p1 t1) (B p2 t2) =
    aeq' (patternCtx ctx) p1 p2
    && aeq' (incrLevelCtx ctx) t1 t2

  isPat _ = inconsistentDisjointSet

  close ctx b (B p t) =
    B (close (patternCtx ctx) b p) (close (incrLevelCtx ctx) b t)

  open ctx b (B p t) =
    B (open (patternCtx ctx) b p) (open (incrLevelCtx ctx) b t)

  nthPatFind b = error $ "Binding " ++ show b ++ " used as a pattern"
  namePatFind b = error $ "Binding " ++ show b ++ " used as a pattern"

  swaps' ctx perm (B p t) =
    B (swaps' (patternCtx ctx) perm p)
      (swaps' (incrLevelCtx ctx) perm t)

  freshen' ctx (B p t) = do
    (p', perm1) <- freshen' (patternCtx ctx) p
    (t', perm2) <- freshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) perm1 t)
    return (B p' t', perm1 <> perm2)
