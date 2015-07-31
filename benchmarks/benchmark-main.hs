module Main where

import Criterion.Main

import BenchLam (freshenEtaTermBench)

main :: IO ()
main =
  defaultMain
  [
    bgroup "unbound-generics" [
        freshenEtaTermBench 10
        , freshenEtaTermBench 20
        , freshenEtaTermBench 30
        , freshenEtaTermBench 40
        , freshenEtaTermBench 50
        , freshenEtaTermBench 100
        , freshenEtaTermBench 200
        ]
  ]
