-- |
-- Module     : Unbound.Generics.LocallyNameless.Ignore
-- Copyright  : (c) 2018, Reed Mullanix
-- License    : BSD3 (See LICENSE)
-- Maintainer : Reed Mullanix
-- Stability  : experimental
--
-- Ignores a term for the purposes of alpha-equality and substitution
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Ignore (
    Ignore(..)
    ) where

import Control.DeepSeq (NFData(..))

import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless.Alpha

-- | Ignores a term 't' for the purpose of alpha-equality and substitution
data Ignore t = I t
        deriving (Generic)

instance (NFData t) => NFData (Ignore t) where
    rnf (I t) = rnf t `seq` ()

instance (Show t) => Show (Ignore t) where
    showsPrec prec (I t) = 
        showParen (prec > 0) (showString "<-" 
                              . showsPrec prec t
                              . showString "->")

instance (Show t) => Alpha (Ignore t) where
    aeq' _ _ _ = True
    fvAny' _ _ = pure
    isPat _ = inconsistentDisjointSet
    isTerm _ = mempty
    close _ _ = id
    open _ _ = id
    namePatFind  _ = NamePatFind $ const $ Left 0
    nthPatFind _ = NthPatFind Left
    swaps' _ _ = id
    lfreshen' _ i cont = cont i mempty
    freshen' _ i = return (i, mempty)
    acompare' _ _ _ = EQ