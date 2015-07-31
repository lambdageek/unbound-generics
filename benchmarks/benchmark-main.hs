module Main where

import Criterion.Main

main =
  defaultMain
  [
    bgroup "unbound-generics" [ -- bench "fib 10" $ whnf fib 10
                              ]
  ]
