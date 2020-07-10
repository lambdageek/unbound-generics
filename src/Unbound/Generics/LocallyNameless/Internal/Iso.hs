{-# LANGUAGE RankNTypes #-}
module Unbound.Generics.LocallyNameless.Internal.Iso where

import Data.Profunctor (Profunctor(..))
import Data.Functor.Identity (Identity(..))

data Exchange a b s t = Exchange (s -> a) (b -> t)

instance Functor (Exchange a b s) where
  fmap f (Exchange p q) = Exchange p (f . q)

instance Profunctor (Exchange a b) where
  dimap f g (Exchange h k) = Exchange (h . f ) (g . k)

type Iso s t a b = forall p f . (Profunctor p, Functor f) => p a (f b) -> p s (f t)

type AnIso s t a b = Exchange a b a (Identity b) -> Exchange a b s (Identity t)

iso :: (s -> a) -> (b -> t) -> Iso s t a b
iso sa bt = dimap sa (fmap bt)
{-# INLINE iso #-}

from :: AnIso s t a b -> Iso b a t s
from l = withIso l $  \ sa bt -> iso bt sa
{-# INLINE from #-}

withIso :: AnIso s t a b -> ((s -> a) -> (b -> t) -> r) -> r
withIso ai k =
  case ai (Exchange id Identity) of
   Exchange sa bt -> k sa (runIdentity . bt)
{-# INLINE withIso #-}
