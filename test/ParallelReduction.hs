--
-- We implement the parallel reduction relation e ⇛ e'
-- that is a key to some kinds of confluence proofs for lambda calculi.
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable, MultiParamTypeClasses #-}
module ParallelReduction where

import Control.Applicative 
import Control.Monad.Identity
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Unbound.Generics.LocallyNameless

type Var = Name Expr

-- in this case we just have an untyped lambda calculus
data Expr = V Var
          | Lam (Bind Var Expr)
          | App Expr Expr
          deriving (Show, Generic, Typeable)

instance Alpha Expr

instance Subst Expr Expr where
  isvar (V n) = Just (SubstName n)
  isvar _     = Nothing

run :: FreshMT Identity Expr -> Expr
run = runIdentity . runFreshMT

-- parallel reduction is the compatible closure of cbn beta : (λx.e)f ⇛ {f'/x}e' where e⇛e' and f⇛f'
-- we choose to allow reduction under a lambda.
parStep :: (Applicative m, Fresh m) => Expr -> m Expr
parStep v@(V _) = return v
parStep (App e1 e2) =
  case e1 of
    Lam b -> betaStep e2 b
    _ -> App <$> parStep e1 <*> parStep e2
parStep (Lam b) = do
  (v, e) <- unbind b
  (Lam . (bind v)) <$> parStep e

betaStep :: (Applicative m, Fresh m) => Expr -> Bind Var Expr -> m Expr
betaStep f b = do
  f' <- parStep f
  (v, e) <- unbind b
  e' <- parStep e
  return (subst v f' e')

-- repeatedly take parStep steps until the term doesn't change anymore.
parSteps :: (Applicative m, Fresh m) => Expr -> m Expr
parSteps e = do
  e' <- parStep e
  if (e `aeq` e')
    then return e
    else parSteps e'

ex1 :: Bind Var Expr
ex1 = let
  x = s2n "x"
  in bind x (V x)
ex1' :: (Var, Expr)
ex1' = let
  y = s2n "y"
  in
   (y, V y)

ex2 :: Expr
ex2 = App (Lam ex2_1) ex2_2

ex2_1 :: Bind Var Expr
ex2_1 = let
  x = s2n "x"
  y = s2n "y"
  in
   bind x $ Lam $ bind y $ App (V x) (V y)

ex2_2 :: Expr
ex2_2 = let
  z = s2n "z"
  in
   (Lam $ bind z $ V z)

ident :: Expr
ident = let
  u = s2n "u"
  in Lam $ bind u $ V u

-- same as ex2 but with some extra beta redices in both halves of the application
ex2_alt :: Expr
ex2_alt = App (App ident (Lam ex2_1)) (App (App ident ident) ex2_2)
  
