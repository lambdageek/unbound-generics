-- |
-- Module     : test-stlc
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module Main where

import Unbound.Generics.LocallyNameless

import Calc

import Test.HUnit

test_ex1 :: Test
test_ex1 = TestCase $ assertBool "example 1" (runWhnf emptyEnv ex1 `aeq` (Just $ C 3))

test_ex2_open :: Test
test_ex2_open = TestCase $ assertBool "example 2 (open)" (not $ aeq ex2x ex2y)

test_ex2_closed :: Test
test_ex2_closed = TestCase $ assertBool "example 2 (closed)" (aeq ex2xc ex2yc)

test_ex3 :: Test
test_ex3 = TestCase $ assertBool "example 3" (aeq ex3x ex3y)

test_ex4 :: Test
test_ex4 = TestCase $ assertBool "example 4 (let scoping)" (runWhnf emptyEnv ex4 `aeq` Just ex4_ans)

test_ex5 :: Test
test_ex5 = TestCase $ assertBool "example 5 (let* scoping)" (runWhnf emptyEnv ex5 `aeq` Just ex5_ans)

test_ex6 :: Test
test_ex6 = TestCase $ assertBool "example 6 (free variables)" (anyFreeVarList ex6 `aeq` ex6_ans)

test_ex7 :: Test
test_ex7 = TestCase $ assertBool "example 7 (sorted free variables)" (freeVarList ex7 `aeq` ex7_ans)


main :: IO ()
main = do
  result <- runTestTT $ TestList [test_ex1
                                 , test_ex2_open
                                 , test_ex2_closed
                                 , test_ex3
                                 , test_ex4
                                 , test_ex5
                                 , test_ex6
                                 , test_ex7
                            ]
  if failures result > 0
    then fail "Some tests failed!"
    else return ()
