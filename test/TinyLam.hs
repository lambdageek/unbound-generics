{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, FlexibleContexts #-}
module TinyLam where

import GHC.Generics (Generic)
import Data.Typeable (Typeable)

import Control.Applicative (Applicative(..))
import Control.Monad.Reader
import Data.Monoid (Monoid(..))
import qualified Data.List 

import Test.Tasty
import Test.Tasty.HUnit

import Unbound.Generics.LocallyNameless


type Var = Name Expr

data ArithOp = ArithOp String (Int -> Int -> Int)
             deriving (Typeable, Generic)

instance Show ArithOp where
  show (ArithOp f _) = f

data Expr = V Var
          | I Int
          | Arith ArithOp Expr Expr
          | Lam Fun
          | App Expr Expr
          | If0 Expr Expr Expr
          | Letrec (Bind (Rec (Var, Embed Fun)) Expr)
          deriving (Typeable, Generic, Show)

newtype Fun = Fun (Bind Var Expr)
            deriving (Typeable, Generic, Show)

instance Eq Expr where
  (==) = aeq

instance Eq Fun where
  (==) = aeq

-- leaf instance for ArithOp
instance Alpha ArithOp where
  aeq' _ctx (ArithOp s1 _) (ArithOp s2 _) = s1 == s2
  fvAny' _ctx _nfn x = pure x
  close _ctx _b x = x
  open _ctx _b x = x
  isPat _ = mempty
  isTerm _ = True
  nthPatFind _ = mempty
  namePatFind _ _ = Left 0

  swaps' _ctx _p x = x
  freshen' _ctx x = return (x, mempty)
  lfreshen' _ctx x cont = cont x mempty
  acompare' _ctx (ArithOp s1 _) (ArithOp s2 _) = compare s1 s2

instance Alpha Expr
instance Alpha Fun

type Env = [(Var, Value)]

data Value = VI !Int
           | VClo !Env !Fun
           deriving (Eq, Show) 


emptyEnv :: Env
emptyEnv = []

extendEnv :: Var -> Value -> Env -> Env
extendEnv x v rho = (x,v) : rho

env :: MonadReader Env m => m Env
env = ask

lookupV :: MonadReader Env m => Var -> m Value
lookupV x = env >>= \rho ->
  case Data.List.lookup x rho of
   Just v -> return v
   Nothing -> error $ "unbound variable " ++ show x

eval :: (Fresh m, MonadReader Env m) => Expr -> m Value
eval (V x) = lookupV x
eval (I i) = return $ VI i
eval (Lam f) = env >>= \rho -> return (VClo rho f)
eval (App e1 e2) = do
  v1 <- eval e1
  case v1 of
   (VClo rho (Fun bnd)) -> do
     v2 <- eval e2
     (x, e3) <- unbind bnd
     local (const $ extendEnv x v2 rho) $ eval e3
   _ -> error ("expected a function, but got " ++ show v1)
eval (Arith (ArithOp _ op) e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case (v1, v2) of
   (VI n1, VI n2) -> return $ VI (op n1 n2)
   _ -> error ("expected pair of ints, but got " ++ show v1
               ++ " and " ++ show v2)
eval (If0 e1 e2 e3) = do
  v1 <- eval e1
  case v1 of
   VI 0 -> eval e2
   VI _ -> eval e3
   _ -> error ("expected int, but got " ++ show v1)
eval (Letrec bnd) = do
  (r, ebody) <- unbind bnd
  rho0 <- ask
  let (f, Embed fun) = unrec r
      -- N.B. knot tying
      rho = extendEnv f vclo rho0
      vclo = VClo rho fun
  local (extendEnv f vclo) $ eval ebody

runEval :: Expr -> Value
runEval e = runReader (runFreshMT (eval e)) emptyEnv

ex_f :: Int -> Expr
ex_f n = let
  (/*/) = Arith (ArithOp "*" (*))
  (/-/) = Arith (ArithOp "-" (-))
  fact = s2n "fact"
  x = s2n "x"
  body = If0 (V x)
         {-then-} (I 1)
         {-else-} (V x
                   /*/ 
                   App (V fact) (V x /-/ I 1))
  factfun = Fun (bind x body)
  in Letrec $ bind (rec (fact, Embed factfun))
     (App (V fact) (I n))

test_ex_f0 :: TestTree
test_ex_f0 =
  testCase "eval (fact 0) = 1"
  $ assertEqual "" (runEval (ex_f 0)) (VI 1)

test_ex_f5 :: TestTree
test_ex_f5 =
  testCase "eval (fact 5) = 120"
  $ assertEqual "" (runEval (ex_f 5)) (VI 120)

test_tinyLam :: TestTree
test_tinyLam =
  testGroup "tinyLam"
  [ test_ex_f0
  , test_ex_f5
  ]
