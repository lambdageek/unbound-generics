{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, MultiParamTypeClasses #-}
module TestIgnore (test_ignore) where

import Data.Typeable(Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

import AlphaAssertions

import Test.Tasty
import Test.Tasty.HUnit

type Var = Name Term

type SourcePos = (Int, Int)
data SourceSpan = SourceSpan 
    { start :: SourcePos
    , end :: SourcePos
    }
    deriving (Show)

data Term
    = Var Var
    | Lam (Bind Var Term)
    | App Term Term
    | Ann (Ignore SourceSpan) Term
    | NoSubst (Ignore Term)
    deriving (Show, Typeable, Generic)

instance Alpha Term
instance Subst Term Term where
    isvar (Var x) = Just $ SubstName x
    isvar _ = Nothing

lam :: Var -> Term -> Term
lam x t = Lam (bind x t)

x :: Var
x = s2n "x"

y :: Var
y = s2n "y"

t1 :: Term
t1 = Ann (ignore (SourceSpan (0,0) (0,1))) (Var x)

t2 :: Term
t2 = Ann (ignore (SourceSpan (1,0) (1,10))) (Var x)

test_ignore :: TestTree
test_ignore =
    testCase "<-(0,0) (0,1)-> x = <-(1,0) (1,10)-> x" $ assertAeq t1 t2