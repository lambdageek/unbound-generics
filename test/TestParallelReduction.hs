module TestParallelReduction (test_parallelReduction) where

import Test.Tasty
import Test.Tasty.HUnit

import Unbound.Generics.LocallyNameless (Alpha, subst, aeq)

import ParallelReduction


assertAeq :: (Alpha t, Show t) => t -> t -> Assertion
assertAeq x y = assertBool (show x ++ " not alpha equivalent to " ++ show y) (x `aeq` y)

test_ex1 :: TestTree
test_ex1 = testCase "simple substitution" $ assertAeq (subst (fst ex1') (Lam ex1) (snd ex1')) (Lam ex1)

test_ex2 :: TestTree
test_ex2 = testCase "parallel reduction" $ assertAeq (run (parSteps ex2)) (run (parSteps ex2_alt))

test_parallelReduction :: TestTree
test_parallelReduction =
  testGroup "parallel reduction"
  [test_ex1
  , test_ex2
  ]

