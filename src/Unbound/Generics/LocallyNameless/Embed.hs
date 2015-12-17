{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Embed
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Embed' t@ contains a term @t@.
{-# LANGUAGE DeriveGeneric, TypeFamilies #-}
module Unbound.Generics.LocallyNameless.Embed where

import Control.Applicative (pure, (<$>))
import Control.DeepSeq (NFData(..))
import Data.Monoid (mempty, All(..))
import Data.Profunctor (Profunctor(..))

import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Internal.Iso (iso)

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
newtype Embed t = Embed t deriving (Eq, Ord, Generic)

class IsEmbed e where
  -- | The term type embedded in the embedding 'e'
  type Embedded e :: *
  -- | Insert or extract the embedded term.
  -- If you're not using the lens library, see 'Unbound.Generics.LocallyNameless.Operations.embed'
  -- and 'Unbound.Generics.LocallyNameless.Operations.unembed'
  -- otherwise 'embedded' is an isomorphism that you can use with lens.
  -- @
  -- embedded :: Iso' (Embedded e) e
  -- @
  embedded :: (Profunctor p, Functor f) => p (Embedded e) (f (Embedded e)) -> p e (f e)

instance IsEmbed (Embed t) where
  type Embedded (Embed t) = t
  embedded = iso (\(Embed t) -> t) Embed
  
instance NFData t => NFData (Embed t) where
  rnf (Embed t) = rnf t `seq` ()

instance Show a => Show (Embed a) where
  showsPrec _ (Embed a) = showString "{" . showsPrec 0 a . showString "}"

instance Alpha t => Alpha (Embed t) where
  isPat (Embed t) = if getAll (isTerm t) then mempty else inconsistentDisjointSet

  isTerm _ = All False

  isEmbed (Embed t) = getAll (isTerm t)

  swaps' ctx perm (Embed t) =
    if isTermCtx ctx
    then Embed t
    else Embed (swaps' (termCtx ctx) perm t)

  freshen' ctx p =
    if isTermCtx ctx
    then error "LocallyNameless.freshen' called on a term"
    else return (p, mempty)

  lfreshen' ctx p cont =
    if isTermCtx ctx
    then error "LocallyNameless.lfreshen' called on a term"
    else cont p mempty


  aeq' ctx (Embed x) (Embed y) = aeq' (termCtx ctx) x y

  fvAny' ctx afa ex@(Embed x) =
    if isTermCtx ctx
    then pure ex
    else Embed <$> fvAny' (termCtx ctx) afa x

  close ctx b (Embed x) =
    if isTermCtx ctx
    then error "LocallyNameless.close on Embed"
    else Embed (close (termCtx ctx) b x)

  open ctx b (Embed x) =
    if isTermCtx ctx
    then error "LocallyNameless.open on Embed"
    else Embed (open (termCtx ctx) b x)

  nthPatFind _ = mempty
  namePatFind _ = mempty

  acompare' ctx (Embed x) (Embed y) = acompare' (termCtx ctx) x y
