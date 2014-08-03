{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Unsafe
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Dangerous operations that may disturb the invariants of
-- "Unbind.Generics.LocallyNameless" or of your AST.
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Unsafe
       (
         unsafeUnbind
       ) where

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind

-- | A destructor for binders that does /not/ guarantee fresh
--   names for the binders.
unsafeUnbind :: (Alpha p, Alpha t) => Bind p t -> (p, t)
unsafeUnbind (B p t) = (p, open initialCtx p t)
       
