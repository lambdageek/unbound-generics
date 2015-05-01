{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module TestShiftEmbed (test_shiftEmbed) where

import Prelude hiding (pi)

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless
import qualified Unbound.Generics.PermM as PermM

import AlphaAssertions

import Test.Tasty
import Test.Tasty.HUnit

type Var = Name Term

data Term
  = V Var
  | Pi (Bind (Var, Embed Term) Term)
  | LetRec (Bind (Rec Decl) Term)
    deriving (Show, Generic, Typeable)

data Decl =
  -- a recursive declaration  x : A = m
  -- where x may occur in m but not in A
  Decl {
    declVar :: Var
    , declClass :: Shift (Embed Term)
    , declVal :: Embed Term
    }
  deriving (Show, Generic, Typeable)

instance Alpha Term
instance Alpha Decl

x, y, z :: Var
x = s2n "x"
y = s2n "y"
z = s2n "z"

pi :: Var -> Term -> Term -> Term
pi v a b = Pi $ bind (v, embed a) b

letrec :: Decl -> Term -> Term
letrec d e = LetRec $ bind (rec d) e

decl :: Var -> Term -> Term -> Decl
decl v klass e = Decl v (embed klass) (embed e)


test_shiftEmbed =
  testGroup "Embedded and Shifted terms"
  [
    testGroup "Embed"
    [
      testCase "(pi x:x . x) = (pi y:x . y)" $ let m1 = pi x (V x) (V x)
                                                   m2 = pi y (V x) (V y)
                                               in assertAeq m1 m2
    , testCase "(letrec x : x = x in x) = (letrec y : x = y in y)"
      $ let m1 = letrec (decl x (V x) (V x)) (V x)
            m2 = letrec (decl y (V x) (V y)) (V y)
        in assertAeq m1 m2
    , testCase "pi x : z . (letrec x : x = x in x) = pi y : z . (letrec x : y = x in x)"
      $ let m1 = pi x (V z) $ letrec (decl x (V x) (V x)) (V x)
            m2 = pi y (V z) $ letrec (decl x (V y) (V x)) (V x)
        in assertAeq m1 m2
    ]
  ]
