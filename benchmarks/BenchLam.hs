-- | Untyped lambda calc for benchmarking
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module BenchLam where

import Control.Applicative
import Control.Monad (replicateM)
import Data.List (foldl')

import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Control.DeepSeq (NFData(..), deepseq)
import Criterion (Benchmark, env, bench, nf)

import Unbound.Generics.LocallyNameless

type Var = Name Term

data Term =
  V !Var
  | App !Term !Term
  | Lam !(Bind Var Term)
    deriving (Show, Generic, Typeable)

instance Alpha Term
instance NFData Term


-- | lambda abstract over all the given vars
lams :: [Var] -> Term -> Term
lams [] = id
lams (v:vs) = Lam . bind v . lams vs

-- | apply the given term to the given terms
apps :: Term -> [Term] -> Term
apps = foldl' App

-- eta-expand a term a given number of times
etaN :: Fresh m => Term -> Int -> m Term
etaN m n = do
  vs <- replicateM n (fresh $ s2n "v")
  let ms = map V vs
  return (lams vs $ apps m ms)

-- | While the head is a lambda, descend under it and then do something;
-- then close all the lambdas back up.
workHeadUnderLams :: Fresh m => (Term -> m Term) -> (Term -> m Term)
workHeadUnderLams comp = go
  where
    go m =
      case m of
      Lam bnd -> do
        (x, m') <- unbind bnd
        m'' <- go m'
        return $ Lam $ bind x m''
      _ -> comp m

freshNeutralTermHead :: (Applicative m, Fresh m) => Term -> m Term
freshNeutralTermHead (App m n) = App <$> freshNeutralTermHead m <*> pure n
freshNeutralTermHead (V v) = V <$> fresh v
freshNeutralTermHead lam@(Lam {}) = return lam

-- | A benchmark that creates an eta expansion of the term "x" of a given size
-- and then freshens the "x" by traversing down below all the lambdas.
--
-- Every time we go under a lambda, we freshen the body, so to go
-- under N lambdas, we do O(N²) work.
freshenEtaTermBench :: Int -> Benchmark
freshenEtaTermBench n =
  let name = "freshen eta term of size " ++ show n
  in name `deepseq` env setup $ \m ->
  bench name $ nf (runFreshM . workHeadUnderLams freshNeutralTermHead) m
  where
    setup = return $ runFreshM $ etaN (V $ s2n "x") n
