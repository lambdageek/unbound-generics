module AlphaAssertions where

import Test.Tasty.HUnit

import Unbound.Generics.LocallyNameless

assertAeq :: (Alpha t, Show t) => t -> t -> Assertion
assertAeq x y = assertBool (show x ++ " not alpha equivalent to " ++ show y) (x `aeq` y)

assertAcompare :: (Alpha t, Show t) => t -> t -> Ordering -> Assertion
assertAcompare x y o =
  let o' = acompare x y
  in  assertBool (show x ++ " not alpha-" ++ show o' ++ " to " ++ show y ++ ", but alpha-" ++ show o) (o' == o)
