module Main where

import Test.HUnit

import Unbound.Generics.LocallyNameless (subst, aeq)

import ParallelReduction




test_ex1 :: Test
test_ex1 = TestCase $ assertBool "simple substitution" (subst (fst ex1') (Lam ex1) (snd ex1') `aeq` (Lam ex1))

test_ex2 :: Test
test_ex2 = TestCase $ assertBool "parallel reduction" (run (parSteps ex2) `aeq` run (parSteps ex2_alt))

main :: IO ()
main = do
  result <- runTestTT $ TestList [test_ex1
                                 , test_ex2
                                 ]
  if failures result > 0
    then fail "Some tests failed!"
    else return ()
