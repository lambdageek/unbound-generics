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
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Bind (
  -- * Name binding
  Bind(..)
  ) where

import Control.Applicative (Applicative(..), (<$>))
import Control.DeepSeq (NFData(..))
import Data.Monoid ((<>), All(..))

import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless.Alpha

-- | A term of type @'Bind' p t@ is a term that binds the free
-- variable occurrences of the variables in pattern @p@ in the term
-- @t@.  In the overall term, those variables are now bound. See also
-- 'Unbound.Generics.LocallyNameless.Operations.bind' and
-- 'Unbound.Generics.LocallyNameless.Operations.unbind' and
-- 'Unbound.Generics.LocallyNameless.Operations.lunbind'
data Bind p t = B p t
              deriving (Generic)

instance (NFData p, NFData t) => NFData (Bind p t) where
  rnf (B p t) = rnf p `seq` rnf t `seq` ()

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

  fvAny' ctx nfn (B p t) = B <$> fvAny' (patternCtx ctx) nfn p
                             <*> fvAny' (incrLevelCtx ctx) nfn t

  isPat _ = inconsistentDisjointSet

  isTerm (B p t) = (All $ isConsistentDisjointSet $ isPat p) <> isTerm t

  close ctx b (B p t) =
    B (close (patternCtx ctx) b p) (close (incrLevelCtx ctx) b t)

  open ctx b (B p t) =
    B (open (patternCtx ctx) b p) (open (incrLevelCtx ctx) b t)

  nthPatFind _ = error "Binding used as a pattern"
  
  namePatFind _ = error "Binding used as a pattern"

  swaps' ctx perm (B p t) =
    B (swaps' (patternCtx ctx) perm p)
      (swaps' (incrLevelCtx ctx) perm t)

  freshen' ctx (B p t) = do
    (p', perm1) <- freshen' (patternCtx ctx) p
    (t', perm2) <- freshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) perm1 t)
    return (B p' t', perm1 <> perm2)
  {-# INLINE freshen' #-}

  lfreshen' ctx (B p t) cont =
    lfreshen' (patternCtx ctx) p $ \p' pm1 ->
    lfreshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) pm1 t) $ \t' pm2 ->
    cont (B p' t') (pm1 <> pm2)

  acompare' ctx (B p1 t1) (B p2 t2) =
    acompare' (patternCtx ctx) p1 p2 <> acompare' (incrLevelCtx ctx) t1 t2
