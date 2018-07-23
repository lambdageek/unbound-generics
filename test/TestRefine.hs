{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, MultiParamTypeClasses #-}
module TestRefine (test_refine) where

import Data.Typeable (Typeable)
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

import AlphaAssertions

import Test.Tasty
import Test.Tasty.HUnit

-- Regular variables range over terms
type Var = Name Term

-- Metavariables range over extracts
type MetaVar = Name Extract

data Term 
    = Var Var
    | Hole MetaSubst MetaVar -- Every occurance of a metavariable must subst away fvs of extract
    | Lam (Bind Var Term)
    | App Term Term
    deriving (Generic, Typeable, Show)

-- Extracts represent code extracted via refinement
newtype Extract = Extract { extractTerm :: Term }
    deriving (Generic, Typeable, Show)

newtype MetaSubst = MetaSubst { unMetaSubst :: [(Var, Term)] }
    deriving (Generic, Typeable, Show)

instance Alpha Term
instance Alpha Extract
instance Alpha MetaSubst

instance Subst Term Term where
    isvar (Var x) = Just $ SubstName x
    isvar _ = Nothing

instance Subst Extract Term where
    isCoerceVar (Hole ms x) = Just $ SubstCoerce x (Just . applyMetaSubst ms)
    isCoerceVar _ = Nothing

applyMetaSubst :: MetaSubst -> Extract -> Term
applyMetaSubst (MetaSubst ms) e = substs ms $ extractTerm e

instance Subst Term MetaSubst
instance Subst Extract MetaSubst

test_refine :: TestTree
test_refine =
    testCase "subst ?1 x <a/?1>?0 = <a/x>?0"
    $ let h0 = s2n "0" :: MetaVar
          h1 = s2n "1" :: MetaVar
          a = s2n "a" :: Var
          x = s2n "x" :: Var
          e1 = Hole (MetaSubst [(a, Hole (MetaSubst []) h1)]) h0
          e2 = Hole (MetaSubst [(a, Var x)]) h0
      in assertAeq (subst h1 (Extract $ Var x) e1) e2