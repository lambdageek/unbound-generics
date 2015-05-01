{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Shift
-- Copyright  : (c) 2015, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Shift' e@ shifts the scope of the embedded term in @e@ one level outwards.
--
{-# LANGUAGE TypeFamilies #-}
module Unbound.Generics.LocallyNameless.Shift where

import Control.Applicative
import Data.Monoid (Monoid(..))

import Unbound.Generics.LocallyNameless.Alpha (Alpha(..),
                                               decrLevelCtx, isTermCtx,
                                               isZeroLevelCtx,
                                               inconsistentDisjointSet)
import Unbound.Generics.LocallyNameless.Embed (IsEmbed(..))

import Unbound.Generics.LocallyNameless.Internal.Iso (iso)

-- | The type @Shift e@ is an embedding pattern that shifts the scope of the
-- free variables of the embedded term @'Embedded' e@ up by one level.
newtype Shift e = Shift e

instance Functor Shift where
  fmap f (Shift e) = Shift (f e)

instance IsEmbed e => IsEmbed (Shift e) where
  type Embedded (Shift e) = Embedded e
  embedded = iso (\(Shift e) -> e) Shift . embedded
  
instance Show e => Show (Shift e) where
  showsPrec _ (Shift e) = showString "{" . showsPrec 0 e . showString "}"

instance Alpha e => Alpha (Shift e) where
  isPat (Shift e) = if (isEmbed e) then mempty else inconsistentDisjointSet

  isTerm _ = False

  isEmbed (Shift e) = isEmbed e

  swaps' ctx perm (Shift e) = Shift (swaps' (decrLevelCtx ctx) perm e)

  freshen' ctx p =
    if isTermCtx ctx
    then error "LocallyNameless.freshen' called on a term"
    else return (p, mempty)

  lfreshen' ctx p kont =
    if isTermCtx ctx
    then error "LocallyNameless.lfreshen' called on a term"
    else kont p mempty

  aeq' ctx (Shift e1) (Shift e2) = aeq' ctx e1 e2

  fvAny' ctx afa (Shift e) = Shift <$> fvAny' ctx afa e

  close ctx b se@(Shift e) =
    if isTermCtx ctx
    then error "LocallyNameless.close on Shift"
    else if isZeroLevelCtx ctx
         then
           -- consider type A = Rec (Name t, Shift (Embed e), (Embed e))
           --  (ie the 2nd element of the tuple is not allowed to refer to itself,
           --   but the third is)
           -- if we have (x, e1, e2) and we apply 'rec' to it,
           -- we must close the tuple with respect to itself.
           -- in that case, the ctxLevel is 0 and so none of the names in
           -- e1 need be bound.
           -- on the other hand once we go to
           --   Bind P (Bind A B) for some P and B,
           -- the free vars of e1 in A are bound by P.
           se
         else Shift (close (decrLevelCtx ctx) b e)

  open ctx b se@(Shift e) =
    if isTermCtx ctx
    then error "LocallyNameless.open on Shift"
    else if isZeroLevelCtx ctx
         then se
         else Shift (open (decrLevelCtx ctx) b e)

  nthPatFind (Shift e) i = nthPatFind e i
  namePatFind (Shift e) x = namePatFind e x


  acompare' ctx (Shift x) (Shift y) = acompare' ctx x y

  
