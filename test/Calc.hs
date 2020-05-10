-- |
-- Module     : Calc
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
{-# LANGUAGE CPP, DeriveGeneric, DeriveDataTypeable #-}
module Calc where

#if MIN_VERSION_base(4,9,0) && !MIN_VERSION_base(4,11,0)
import Control.Monad.Fail (MonadFail)
#endif
import Control.Arrow (second)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)

-- variables will range over expressions
type Var = Name Expr

-- expression is either a variable, a constant int, a summation of two
-- expressions, a list of variables bound to expressions that may
-- occur in the body of an expression (where the expressions in the
-- list of bindings refer to an outer scope), or a sequence of nested bindings
-- where each binding expression can refer to previously bound variables.
data Expr = V Var
          | C Int
          | Add Expr Expr
          | Let (Bind [(Var, Embed Expr)] Expr)
          | LetStar (Bind LetStarBinds Expr)
          deriving (Generic, Typeable, Show)

data LetStarBinds = EmptyLSB
                  | ConsLSB (Rebind (Var, Embed Expr) LetStarBinds)
                  deriving (Generic, Typeable, Show)

instance Alpha Expr
instance Alpha LetStarBinds

mkVar :: String -> Var
mkVar = s2n

anyFreeVarList :: Alpha a => a -> [AnyName]
anyFreeVarList = toListOf fvAny

freeVarList :: (Alpha a, Typeable b) => a -> [Name b]
freeVarList = toListOf fv

-- smart constructor for Let
mkLet :: [(Var, Expr)] -> Expr -> Expr
mkLet binds body = Let (bind (map (second Embed) binds) body)

-- smart constructor for Let*
mkLetStar :: [(Var, Expr)] -> Expr -> Expr
mkLetStar binds body = LetStar (bind (mkLsb binds) body)
  where
    mkLsb [] = EmptyLSB
    mkLsb ((v,e):rest) = ConsLSB (rebind (v, Embed e) (mkLsb rest))

-- environments are partial maps from (free) variables to expressions.
type Env = Var -> Maybe Expr

emptyEnv :: Env
emptyEnv = const Nothing

extendEnv :: Var -> Expr -> Env -> Env
extendEnv v e rho w =
  if v == w then Just e else rho w

whnf :: (MonadFail m, Fresh m) => Env -> Expr -> m Expr
whnf rho (V v) = case rho v of
  Just e -> return e
  Nothing -> fail $ "unbound variable " ++ show v
whnf _rho (C i) = return (C i)
whnf rho (Add e1 e2) = do
  v1 <- whnf rho e1
  v2 <- whnf rho e2
  add v1 v2
  where add :: MonadFail m => Expr -> Expr -> m Expr
        add (C i1) (C i2) = return (C $ i1 + i2)
        add _ _ = fail "add of two non-integers"
whnf rho0 (Let b) = do
  (binds, body) <- unbind b
  binds' <- mapM (\(v, Embed e) -> do
                     e' <- whnf rho0 e
                     return (v, e')) binds
  let rho' = foldl (\rho (v,e) -> extendEnv v e rho) rho0 binds'
  whnf rho' body
whnf rho0 (LetStar b) = do
  (lsb, body) <- unbind b
  rho' <- whnfLsb lsb rho0
  whnf rho' body

whnfLsb :: (MonadFail m, Fresh m) => LetStarBinds -> Env -> m Env
whnfLsb EmptyLSB = return
whnfLsb (ConsLSB rbnd) = \rho -> do
  let ((v, Embed e), lsb) = unrebind rbnd
  e' <- whnf rho e
  whnfLsb lsb (extendEnv v e' rho)

runWhnf :: Env -> Expr -> Maybe Expr
runWhnf rho e = runFreshMT (whnf rho e)

ex1 :: Expr
ex1 = Add (C 1) (C 2)

ex2x :: Expr
ex2x = V (mkVar "x")

ex2y :: Expr
ex2y = V (mkVar "y")

ex2xc :: Expr
ex2xc = close initialCtx (namePatFind (mkVar "x")) ex2x

ex2yc :: Expr
ex2yc = close initialCtx (namePatFind (mkVar "y")) ex2y

ex3x :: Expr
ex3x = let x = mkVar "x"
       in mkLet [(x, (C 1))] $ Add (V x) (C 2)

ex3y :: Expr
ex3y = let y = mkVar "y"
       in mkLet [(y, (C 1))] $ Add (V y) (C 2)

ex4 :: Expr
ex4 = let
  x = mkVar "x"
  y = mkVar "y"
  in
   mkLet [(y, (C 5))]
   $ mkLet [(y, (C 200))
           , (x, (Add (V y) -- refers to the outer y
                  (C 6)))]
   $ Add (V x) (V x) -- expect (C 22), not (C 412)

ex4_ans :: Expr
ex4_ans = C 22
   
ex5 :: Expr
ex5 = let
  x = mkVar "x"
  y = mkVar "y"
  in
   mkLet [(y, (C 5))]
   $ mkLetStar [(y, (C 200))
               , (x, (Add (V y) -- refers to the inner y
                      (C 6)))]
   $ Add (V x) (V x) -- expect (C 412), not (C 22)

ex5_ans :: Expr
ex5_ans = C 412

ex6 :: [Expr]
ex6 = [V (mkVar "x"), V (mkVar "z"), mkLet [(mkVar "y", C 1)] (V (mkVar "y"))]

ex6_ans :: [AnyName]
ex6_ans = [AnyName (mkVar "x"), AnyName (mkVar "z")]

ex7 :: [Expr]
ex7 = [V (mkVar "x"), V (mkVar "z"), mkLet [(mkVar "y", C 1)] (V (mkVar "y"))]

ex7_ans :: [Var]
ex7_ans = [mkVar "x", mkVar "z"]
