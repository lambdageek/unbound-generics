{-# LANGUAGE MultiParamTypeClasses, DeriveGeneric, DeriveDataTypeable #-}

module TestSubstBind  where

import Test.Tasty
import Unbound.Generics.LocallyNameless
import Data.Typeable (Typeable)
import GHC.Generics (Generic)


import Test.QuickCheck
import Test.Tasty.QuickCheck (testProperty)
import Unbound.Generics.LocallyNameless.Unsafe (unsafeUnbind)

import AlphaProperties 

type Var = Name Expr

data Expr = V Var | Lam (Bind Var Expr) | I Int | App Expr Expr
  deriving (Generic, Typeable, Show)

instance Alpha Expr

instance Subst Expr Expr where
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing


instance Arbitrary Expr where
  arbitrary = sized arbitrarySizedExpr

  shrink (I i) = I <$> shrink i
  shrink (Lam bndExp) = 
    (substBind bndExp <$> [I 0, V x, V y, V z]) -- does the problem persist with the binder removed?
     ++ (Lam <$> underBinder shrink bndExp) -- shrink under the binder
  shrink (f `App` a) = [f, a] ++ (App <$> shrink f <*> shrink a)
  shrink _ = []

underBinder :: (Monad m) => (Expr -> m Expr) -> Bind Var Expr -> m (Bind Var Expr)
underBinder op bndExp = let 
  (name, bod) = unsafeUnbind bndExp -- Should be safe since no freshnames are invoked
  in do
    bod' <- op bod
    pure $ bind name bod'

arbitrarySizedExpr :: Int -> Gen Expr
arbitrarySizedExpr i | i < 1 = do 
  n <- arbitrary 
  var <- elements [x,y,z]
  elements [I n, V $ var]
arbitrarySizedExpr i = do 
  rest <- arbitrarySizedExpr (i - 1)
  var <- elements [x,y,z]
  n <- arbitrary 
  f <- arbitrarySizedExpr (i `div` 2) -- TODO: reorganize better
  a <- arbitrarySizedExpr (i `div` 2)
  elements [Lam $ bind var rest, f `App` a, I n, V $ var]


x,y,z :: Var
x = s2n "x"
y = s2n "y"
z = s2n "z"


smallStep :: Expr -> Maybe Expr
smallStep ((Lam bndBod) `App` a) = Just $ substBind bndBod a
smallStep (f `App` a) = 
  case (smallStep f, smallStep a) of
    (Nothing, Nothing) -> Nothing
    (Just f', _) -> Just $ f' `App` a
    (Nothing, Just a') -> Just $ f `App` a'
smallStep (Lam bndBod) = Lam <$> underBinder smallStep bndBod
smallStep _ = Nothing -- no step


smallStep' :: (Fresh m) => Expr -> m (Maybe Expr)
smallStep' ((Lam bndBod) `App` a) = do
  (name, bod) <- unbind bndBod
  pure $ Just $ subst name a bod
smallStep' (f `App` a) = do
  mf' <- smallStep' f
  ma' <- smallStep' a
  case (mf', ma') of
    (Nothing, Nothing) -> pure $ Nothing
    (Just f', _) -> pure $ Just $ f' `App` a
    (Nothing, Just a') -> pure $ Just $ f `App` a'
smallStep' (Lam bndBod) = do
  (name, bod) <- unbind bndBod
  mbod' <- smallStep' bod
  case mbod' of
    Nothing -> pure $ Nothing
    Just bod' -> pure $ Just $ Lam $ bind name bod'
smallStep' _ = pure $ Nothing -- no step


expbindProp ::  Expr -> Property
expbindProp e = smallStep e =~= runFreshM (smallStep' e)

test_substBind :: TestTree
test_substBind = testGroup "substBind"
          [testProperty "substBind matches unbind subst" $ expbindProp]
