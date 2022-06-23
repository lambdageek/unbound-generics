module AlphaProperties where

import Unbound.Generics.LocallyNameless (fv, aeq, Name, Alpha)

import Test.Tasty.QuickCheck (counterexample, Property, testProperty)

import Data.Typeable (Typeable)

import Data.Monoid (Any(..))
import Unbound.Generics.LocallyNameless.Internal.Fold (foldMapOf, toListOf)



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