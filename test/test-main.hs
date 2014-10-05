module Main where

import Test.Tasty

import TestCalc
import TestParallelReduction

main = defaultMain $ testGroup "unboundGenerics"
       [
         test_calc
       , test_parallelReduction
       ]
