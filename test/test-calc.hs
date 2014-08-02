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
test_ex1 = TestCase $ assertBool "example 1" (whnf emptyEnv ex1 `aeq` (Just $ C 3))

test_ex2_open :: Test
test_ex2_open = TestCase $ assertBool "example 2 (open)" (not $ aeq ex2x ex2y)

test_ex2_closed :: Test
test_ex2_closed = TestCase $ assertBool "example 2 (closed)" (aeq ex2xc ex2yc)

main :: IO ()
main = do
  result <- runTestTT $ TestList [test_ex1
                                 , test_ex2_open
                                 , test_ex2_closed
                            ]
  if failures result > 0
    then fail "Some tests failed!"
    else return ()
