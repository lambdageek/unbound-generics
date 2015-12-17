{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}
module PropOpenClose (test_openClose) where

import Control.Applicative (Applicative(..), (<$>))
import Data.Monoid (Any(..))
import Data.Typeable (Typeable)
import GHC.Generics (Generic)

import Test.QuickCheck
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.QuickCheck (testProperty)

import Unbound.Generics.LocallyNameless
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)

----------------------------------------
-- Property testing utilities

isFreeIn :: (Typeable a, Alpha b) => Name a -> b -> Bool
isFreeIn = elementOf fv
  where
    elementOf l = anyOf l . (==)
    anyOf l f = getAny . foldMapOf l (Any . f)

notFreeIn :: (Typeable a, Alpha b) => Name a -> b -> Bool
notFreeIn v = not . isFreeIn v

(=~=) :: (Alpha a, Show a) => a -> a -> Property
x =~= y = counterexample (show x ++ " not alpha equivalent to " ++ show y) (x `aeq` y)

(/~@) :: (Typeable a, Alpha b, Show b) => Name a -> b -> Property
v /~@ t = counterexample (show v ++ " is free in " ++ show t) (v `notFreeIn` t)

-- Wrapper around 'Name a' that has an Arbitrary instance that generates free names.
-- Note that this doesn't guarantee /freshness/.  The name may clash with some other one.
-- But it will never be a bound name.
newtype FreeName a = FreeName {getFreeName :: Name a}
                     deriving (Show)

instance Arbitrary (FreeName a) where
  arbitrary = do
    s <- listOf1 (elements ['a'..'z'])
    n <- arbitrary
    return $ FreeName $ makeName s n
  shrink = const []

----------------------------------------
-- example data structure, with no bound names.

data T a = Leaf !a
         | V !(Name (T a))
         | B !(T a) !(T a)
         deriving (Show, Typeable, Generic)

instance (Typeable a, Alpha a) => Alpha (T a)

instance Arbitrary a => Arbitrary (T a) where
  arbitrary =
    oneof
    [
      Leaf <$> arbitrary
    ,(V . getFreeName) <$> arbitrary
    , B <$> arbitrary <*> arbitrary
    ]

-- generator that picks out one of the free variables of a tree
arbVarsOf :: (Alpha a, Typeable a) => T a -> Gen (Name (T a))
arbVarsOf t =
  let vs = toListOf fv t
  in  elements vs

-- spec for free variables of a tree.
-- fvSpec :: Traversal' (T a) (Name (T a))
fvSpec :: Applicative f => (Name (T a) -> f (Name (T a))) -> T a -> f (T a)
fvSpec f t =
  case t of
   Leaf {} -> pure t
   V v -> V <$> f v
   B t1 t2 -> B <$> fvSpec f t1 <*> fvSpec f t2

----------------------------------------
-- Properties

-- every tree is alpha-equivalent to itself
prop_refl :: T Int -> Property
prop_refl x = x =~= x

-- generic fv gives the same answer as fvSpec
prop_fv_spec :: T Int -> Property
prop_fv_spec t = toListOf fv t === toListOf fvSpec t
  
-- if a name is already free opening it has no effect
prop_open_idempotent :: T Int -> Property
prop_open_idempotent t =
  forAll (arbVarsOf t) $ \v -> open initialCtx (nthPatFind v) t =~= t

-- if you close over a variable, then it is no longer free.
prop_close_binds :: T Int -> Property
prop_close_binds t =
  (not $ null $ toListOf fvAny t) ==>
  forAll (arbVarsOf t) $ \v -> v /~@ close initialCtx v t

----------------------------------------
-- Test group

test_openClose :: TestTree
test_openClose =
  testGroup "QuickCheck properties"
  [
    testProperty "reflexivity" prop_refl
  , testProperty "fv specification" prop_fv_spec
  , testProperty "open idempotency" prop_open_idempotent
  , testProperty "closing binds variables" prop_close_binds
  ]
