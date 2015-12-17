{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : TestTH
-- Copyright  : (c) 2015, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Test of 'makeClosedAlpha' splice.
{-# LANGUAGE TemplateHaskell #-}
module TestTH (test_TH) where

import Test.Tasty
import Test.Tasty.HUnit
import AlphaAssertions

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Unbound.Generics.LocallyNameless.TH



data K =
  KT
  | KArr K K
    deriving (Eq, Ord, Show)

$(makeClosedAlpha ''K)

kt, kF, kG :: K
kt = KT
kF = KT `KArr` KT
kG = kF `KArr` KT

emptyPat :: [Name ()]
emptyPat = []

test_TH :: TestTree
test_TH = testGroup "TH makeClosedAlpha splice"
          [ testCase "TH aeq" $ assertAeq kt kt
          , testCase "TH acompare" $ assertAcompare kt kF (compare kt kF)
          , testCase "TH fvAny kG" $ assertEqual "" (toListOf fvAny kG) []
          , testCase "TH close" $ assertEqual "" (close initialCtx (namePatFind emptyPat) kt) kt
          , testCase "TH open" $ assertEqual "" (open initialCtx (nthPatFind emptyPat) kG) kG
          , testCase "TH isTerm" $ assertEqual "" (isTerm kF) True
          , testCase "TH isPat"
            $ assertBool "isNullDisjointSEt (isPat kF)" (isNullDisjointSet $ isPat kF)
          ]
