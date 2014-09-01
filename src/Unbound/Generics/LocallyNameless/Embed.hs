{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Embed
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Embed' t@ contains a term @t@.
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Embed where

import Control.Applicative ((<$>))
import Data.Monoid (mempty)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless.Alpha

-- | @Embed@ allows for terms to be /embedded/ within patterns.  Such
--   embedded terms do not bind names along with the rest of the
--   pattern.  For examples, see the tutorial or examples directories.
--
--   If @t@ is a /term type/, then @Embed t@ is a /pattern type/.
--
--   @Embed@ is not abstract since it involves no binding, and hence
--   it is safe to manipulate directly.  To create and destruct
--   @Embed@ terms, you may use the @Embed@ constructor directly.
--   (You may also use the functions 'embed' and 'unembed', which
--   additionally can construct or destruct any number of enclosing
--   'Shift's at the same time.)
newtype Embed t = Embed t deriving (Eq, Generic)

instance Show a => Show (Embed a) where
  showsPrec _ (Embed a) = showString "{" . showsPrec 0 a . showString "}"

instance Alpha t => Alpha (Embed t) where
  isPat (Embed t) = if (isTerm t) then mempty else inconsistentDisjointSet

  isTerm _ = False

  isEmbed (Embed t) = isTerm t

  swaps' ctx perm (Embed t) =
    if isTermCtx ctx
    then Embed t
    else Embed (swaps' (termCtx ctx) perm t)

  freshen' ctx p =
    if isTermCtx ctx
    then error "LocallyNameless.freshen' called on a term"
    else return (p, mempty)

  aeq' ctx (Embed x) (Embed y) = aeq' (termCtx ctx) x y

  fvAny' ctx afa (Embed x) = Embed <$> fvAny' (termCtx ctx) afa x

  close ctx b (Embed x) =
    if isTermCtx ctx
    then error "LocallyNameless.close on Embed"
    else Embed (close (termCtx ctx) b x)

  open ctx b (Embed x) =
    if isTermCtx ctx
    then error "LocallyNameless.open on Embed"
    else Embed (open (termCtx ctx) b x)

  nthPatFind _ = Left
  namePatFind _ _ = Left 0
