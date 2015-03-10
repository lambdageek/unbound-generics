module Main where

import Test.Tasty

import TestCalc
import TestParallelReduction
import PropOpenClose
import TinyLam
import TestACompare

main :: IO ()
main = defaultMain $ testGroup "unboundGenerics"
       [
         test_calc
       , test_parallelReduction
       , test_openClose
       , test_tinyLam
       , test_acompare
       ]
