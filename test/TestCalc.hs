-- |
-- Module     : test-stlc
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module TestCalc (test_calc) where

import Unbound.Generics.LocallyNameless

import Calc

import Test.Tasty
import Test.Tasty.HUnit

assertAeq :: (Alpha t, Show t) => t -> t -> Assertion
assertAeq x y = assertBool (show x ++ " not alpha equivalent to " ++ show y) (x `aeq` y)

test_ex1 :: TestTree
test_ex1 = testCase "example 1" $ assertAeq (runWhnf emptyEnv ex1) (Just $ C 3)

test_ex2_open :: TestTree
test_ex2_open = testCase "example 2 (open)" $ assertBool "alpha equivalent" (not $ aeq ex2x ex2y)

test_ex2_closed :: TestTree
test_ex2_closed = testCase "example 2 (closed)" $ assertAeq ex2xc ex2yc

test_ex3 :: TestTree
test_ex3 = testCase "example 3" $ assertAeq ex3x ex3y

test_ex4 :: TestTree
test_ex4 = testCase "example 4 (let scoping)" $ assertAeq (runWhnf emptyEnv ex4) (Just ex4_ans)

test_ex5 :: TestTree
test_ex5 = testCase "example 5 (let* scoping)" $ assertAeq (runWhnf emptyEnv ex5) (Just ex5_ans)

test_ex6 :: TestTree
test_ex6 = testCase "example 6 (free variables)" $ assertAeq (anyFreeVarList ex6) ex6_ans

test_ex7 :: TestTree
test_ex7 = testCase "example 7 (sorted free variables)" $ assertAeq (freeVarList ex7) ex7_ans


test_calc :: TestTree
test_calc =
  testGroup "calc"
  [test_ex1
  , test_ex2_open
  , test_ex2_closed
  , test_ex3
  , test_ex4
  , test_ex5
  , test_ex6
  , test_ex7
  ]

