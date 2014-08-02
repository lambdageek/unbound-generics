-- |
-- Module     : Unbound.Generics.LocallyNameless.Operations
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Operations on terms and patterns that contain names.
module Unbound.Generics.LocallyNameless.Operations (aeq, freshen, swaps, bind, unbind) where

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.PermM

-- | @'aeq' t1 t2@ returns @True@ iff @t1@ and @t2@ are alpha-equivalent terms.
aeq :: Alpha a => a -> a -> Bool
aeq = aeq' initialCtx

-- | Freshen a pattern by replacing all old binding 'Name's with new
--   fresh 'Name's, returning a new pattern and a @'Perm' 'Name'@
--   specifying how 'Name's were replaced.
freshen :: (Alpha p, Fresh m) => p -> m (p, Perm AnyName)
freshen = freshen' (patternCtx initialCtx)

-- Apply the given permutation of variable names to the given pattern.
swaps :: Alpha p => Perm AnyName -> p -> p
swaps = swaps' (patternCtx initialCtx)

  
-- | @'bind' p t@ closes over the variables of pattern @p@ in the term @t@
bind :: (Alpha p, Alpha t) => p -> t -> Bind p t
bind p t = B p (close initialCtx p t)

-- | @'unbind' b@ lets you descend beneath a binder @b :: 'Bind' p t@
-- by returning the pair of the pattern @p@ and the term @t@ where the
-- variables in the pattern have been made globally fresh with respect
-- to the freshness monad @m@.
unbind :: (Alpha p, Alpha t, Fresh m) => Bind p t -> m (p, t)
unbind (B p t) = do
  (p', _) <- freshen p
  return (p', open initialCtx p' t)
