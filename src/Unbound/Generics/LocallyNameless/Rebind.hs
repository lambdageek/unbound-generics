{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Rebind
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- The pattern @'Rebind' p1 p2@ binds the names in @p1@ and @p2@ just as @(p1, p2)@ would,
-- however it additionally also brings the names of @p1@ into scope in @p2@.
--
{-# LANGUAGE DeriveGeneric #-}
module Unbound.Generics.LocallyNameless.Rebind where

import Control.Applicative ((<*>), (<$>))
import Data.Monoid ((<>))
import GHC.Generics

import Unbound.Generics.LocallyNameless.Alpha


-- | @'Rebind' p1 p2@ is a pattern that binds the names of @p1@ and @p2@, and additionally
-- brings the names of @p1@ into scope over @p2@.
--
-- This may be used, for example, to faithfully represent Scheme's @let*@ binding form, defined by:
-- 
-- >  (let* () body) ≙ body
-- >  (let* ([v1, e1] binds ...) body) ≙ (let ([v1, e1]) (let* (binds ...) body))
-- 
-- using the following AST:
--
-- @
-- type Var = Name Expr
-- data Lets = EmptyLets
--           | Bind (Rebind (Var, Embed Expr) Lets)
-- data Expr = ...
--           | LetStar { letStarBindings :: Lets
--                     , letStarBody :: Expr
--                     }
--           | ...
-- @
data Rebind p1 p2 = Rebnd p1 p2
                  deriving (Generic, Eq)

instance (Show p1, Show p2) => Show (Rebind p1 p2) where
  showsPrec paren (Rebnd p1 p2) =
    showParen (paren > 0) (showString "<<"
                           . showsPrec paren p1
                           . showString ">> "
                           . showsPrec 0 p2)

instance (Alpha p1, Alpha p2) => Alpha (Rebind p1 p2) where
  isTerm _ = False

  isPat (Rebnd p1 p2) = isPat p1 <> isPat p2

  swaps' ctx perm (Rebnd p1 p2) =
    Rebnd (swaps' ctx perm p1) (swaps' (incrLevelCtx ctx) perm p2)

  freshen' ctx (Rebnd p1 p2) =
    if isTermCtx ctx
    then error "freshen' on Rebind in Term mode"
    else do
      (p1', perm1) <- freshen' ctx p1
      (p2', perm2) <- freshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) perm1 p2)
      return (Rebnd p1' p2', perm1 <> perm2)

  lfreshen' ctx (Rebnd p q) cont =
    if isTermCtx ctx
    then error "lfreshen' on Rebind in Term mode"
    else
      lfreshen' ctx p $ \ p' pm1 ->
      lfreshen' (incrLevelCtx ctx) (swaps' (incrLevelCtx ctx) pm1 q) $ \ q' pm2 ->
      cont (Rebnd p' q') (pm1 <> pm2)


  aeq' ctx (Rebnd p1 p2) (Rebnd q1 q2) =
    -- XXX TODO: Unbound had (aeq' ctx p2 q2) here.  But that doesn't seem right.
    aeq' ctx p1 q1 && aeq' (incrLevelCtx ctx) p2 q2

  fvAny' ctx afa (Rebnd p1 p2) = Rebnd <$> fvAny' ctx afa p1
                                       <*> fvAny' (incrLevelCtx ctx) afa p2

  open ctx b (Rebnd p1 p2) = Rebnd (open ctx b p1) (open (incrLevelCtx ctx) b p2)
  close ctx b (Rebnd p1 p2) = Rebnd (close ctx b p1) (close (incrLevelCtx ctx) b p2)
