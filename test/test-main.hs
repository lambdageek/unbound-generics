module Main where

import Test.Tasty

import TestCalc
import TestParallelReduction
import PropOpenClose
import TinyLam
import TestACompare
import TestRefine
import TestIgnore
import TestShiftEmbed
import TestTH

main :: IO ()
main = defaultMain $ testGroup "unboundGenerics"
       [
         test_calc
       , test_parallelReduction
       , test_openClose
       , test_refine
       , test_ignore
       , test_tinyLam
       , test_acompare
       , test_shiftEmbed
       , test_TH
       ]
