{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Main where

import GHC.Generics(Generic)
import Data.Typeable(Typeable)

import Unbound.Generics.LocallyNameless

import Test.HUnit

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

ex1 :: Expr
ex1 = Add (C 1) (C 2)

test_ex1 :: Test
test_ex1 = TestCase $ assertBool "example 1" (whnf emptyEnv ex1 `aeq` (Just $ C 3))
  where aeq = aeq' initialCtx

main :: IO ()
main = do
  _ <- runTestTT test_ex1
  return ()
