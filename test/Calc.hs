-- |
-- Module     : Calc
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Calc where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless

type Var = Name Expr

data Expr = V Var
          | C Int
          | Add Expr Expr
          deriving (Generic, Typeable, Show)

instance Alpha Expr

type Env = Var -> Maybe Expr

emptyEnv :: Env
emptyEnv = const Nothing

whnf :: Env -> Expr -> Maybe Expr
whnf rho (V v) = rho v
whnf _rho (C i) = return (C i)
whnf rho (Add e1 e2) = do
  v1 <- whnf rho e1
  v2 <- whnf rho e2
  add v1 v2
  where add :: Expr -> Expr -> Maybe Expr
        add (C i1) (C i2) = return (C $ i1 + i2)
        add _ _ = Nothing

mkVar :: String -> Var
mkVar = s2n

ex1 :: Expr
ex1 = Add (C 1) (C 2)

ex2x :: Expr
ex2x = V (mkVar "x")

ex2y :: Expr
ex2y = V (mkVar "y")

ex2xc :: Expr
ex2xc = close initialCtx (mkVar "x") ex2x

ex2yc :: Expr
ex2yc = close initialCtx (mkVar "y") ex2y

