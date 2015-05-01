{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Rec
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Rec' p@ binds the names in @p@ like @p@ itself would,
-- but additionally, the names in @p@ are scope over @p@.
--
-- The term @'TRec' p@ is shorthand for @'Bind' (Rec p) ()@
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Rec
       (
         Rec
       , rec
       , unrec
       , TRec (..)
       ) where

import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Bind

-- | If @p@ is a pattern type, then @Rec p@ is also a pattern type,
-- which is /recursive/ in the sense that @p@ may bind names in terms
-- embedded within itself.  Useful for encoding e.g. lectrec and
-- Agda's dot notation.
newtype Rec p = Rec p
              deriving (Generic, Eq)

instance Show a => Show (Rec a) where
  showsPrec _ (Rec a) = showString "[" . showsPrec 0 a . showString "]"

-- | @TRec@ is a standalone variant of 'Rec': the only difference is
--   that whereas @'Rec' p@ is a pattern type, @TRec p@
--   is a /term type/.  It is isomorphic to @'Bind' ('Rec' p) ()@.
--
--   Note that @TRec@ corresponds to Pottier's /abstraction/ construct
--   from alpha-Caml.  In this context, @'Embed' t@ corresponds to
--   alpha-Caml's @inner t@, and @'Shift' ('Embed' t)@ corresponds to
--   alpha-Caml's @outer t@.
newtype TRec p = TRec (Bind (Rec p) ())
                 deriving (Generic)

instance Show a => Show (TRec a) where
  showsPrec _ (TRec (B (Rec p) ())) = showString "[" . showsPrec 0 p . showString "]"


instance Alpha p => Alpha (Rec p) where
  isTerm _ = False
  isPat (Rec p) = isPat p

  nthPatFind (Rec p) i = nthPatFind p i
  namePatFind (Rec p) x = namePatFind p x

  open ctx b (Rec p) = Rec (open (incrLevelCtx ctx) b p)
  close ctx b (Rec p) = Rec (close (incrLevelCtx ctx) b p)

instance Alpha p => Alpha (TRec p)

-- | Constructor for recursive patterns.
rec :: Alpha p => p -> Rec p
rec p = Rec (close (patternCtx initialCtx) p p)

-- | Destructor for recursive patterns.
unrec :: Alpha p => Rec p -> p
unrec (Rec p) = open (patternCtx initialCtx) p p
