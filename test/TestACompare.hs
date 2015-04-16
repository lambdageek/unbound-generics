{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module TestACompare where

import Data.Typeable
import GHC.Generics
import Unbound.Generics.LocallyNameless

import Test.Tasty
import Test.Tasty.HUnit

import AlphaAssertions

data Expr
  = V (Name Expr)
  | Add Expr Expr
  | L (Bind (Name Expr) Expr)
  deriving (Show,Generic,Typeable)

instance Alpha Expr

nameA, nameB, nameC :: Name Expr
nameA = s2n "a"
nameB = s2n "b"
nameC = s2n "c"

test_acompare :: TestTree
test_acompare = testGroup "acompare"
   -- Names compare in the obvious way.
   [ testGroup "obvious"
      [testCase "ac1 (a < b)"  $ assertAcompare nameA nameB LT
      ,testCase "ac2 (b = b)" $ assertAcompare nameB nameB EQ
      ,testCase "ac3 (b > a)"  $ assertAcompare nameB nameA GT
      ]
   -- structured date compares lexicographically
   , testGroup "lexicographically"
      [testCase "ac4 (a + a = a + a)" $
        assertAcompare (Add (V nameA) (V nameA)) (Add (V nameA) (V nameA)) EQ
      ,testCase "ac5 (a + a < a + b)" $
        assertAcompare (Add (V nameA) (V nameA)) (Add (V nameA) (V nameB)) LT
      ,testCase "ac6 (a + b > a + a)" $
        assertAcompare (Add (V nameA) (V nameB)) (Add (V nameA) (V nameA)) GT
      ,testCase "ac7 (a + a < b + a)" $
        assertAcompare (Add (V nameA) (V nameA)) (Add (V nameB) (V nameA)) LT
      ,testCase "ac8 (b + a > a + a)" $
        assertAcompare (Add (V nameB) (V nameA)) (Add (V nameA) (V nameA)) GT
      ,testCase "ac9 (b + a > a + b)" $
        assertAcompare (Add (V nameB) (V nameA)) (Add (V nameA) (V nameB)) GT
      ]
   -- comparison goes under binders, alpha-respectingly.
   , testGroup "binders"
      [testCase "ac10 (\\a.a+a = \\b.b+b)" $
        assertAcompare (bind nameA (Add (V nameA) (V nameA)))
                       (bind nameB (Add (V nameB) (V nameB)))
                       EQ
      ,testCase "ac11 (\\a.a+a > \\a.a+b)" $
        assertAcompare (bind nameA (Add (V nameA) (V nameA)))
                       (bind nameA (Add (V nameA) (V nameB)))
                       GT
      ,testCase "ac12 (\\c.c+a < \\a.a+b)" $
        assertAcompare (bind nameC (Add (V nameC) (V nameA)))
                       (bind nameA (Add (V nameA) (V nameB)))
                       LT
      ]
   -- non-matching binders handled alpha-respectingly.
   , testGroup "non-matching binders"
      [testCase "ac13 ((\\a.a `ac` \\a b.a) = (\\c.c `ac` \\a b.a))" $
        assertAcompare (bind [nameA] nameA)
                       (bind [nameA,nameB] nameA)
                       (acompare (bind [nameC] nameC) (bind [nameA,nameB] nameA))
      ,testCase "ac14 ((\\a b.a `ac` \\a.a) = (\\c b.c `ac` \\a.a))" $
        assertAcompare (bind [nameA,nameB] nameA)
                       (bind [nameA] nameA)
                       (acompare (bind [nameC,nameB] nameC) (bind [nameA] nameA))
      ]
   -- non-binding stuff in patterns gets compared
   , testGroup "non-binding stuff"
      [testCase "ac15 (<a> < <b>)" $
          assertAcompare (Embed nameA) (Embed nameB) LT
      ,testCase "ac16 (\\c<a>.c+c < \\c<b>.c+c)" $
        assertAcompare
          (bind (nameC, Embed nameA) (Add (V nameC) (V nameC)))
          (bind (nameC, Embed nameB) (Add (V nameC) (V nameC)))
          LT
      ,testCase "ac17 (\\c<a>.b+b < \\c<b>.a+a)" $
        assertAcompare
          (bind (nameC, Embed nameA) (Add (V nameB) (V nameB)))
          (bind (nameC, Embed nameB) (Add (V nameA) (V nameA)))
          LT
      ]
   ]
