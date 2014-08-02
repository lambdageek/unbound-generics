{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Alpha
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Use the 'Alpha' typeclass to mark types that may contain 'Name's.
{-# LANGUAGE DefaultSignatures, FlexibleContexts #-}
module Unbound.Generics.LocallyNameless.Alpha (
  -- * Name-aware opertions
  Alpha(..)
  -- * Binder variables
  , DisjointSet(..)
  , inconsistentDisjointSet
  , singletonDisjointSet
  , isConsistentDisjointSet
  -- * Implementation details
  , AlphaCtx
  , initialCtx
  ) where

import Data.Function (on)
import Data.Foldable (Foldable(..))
import Data.List (intersect)
import Data.Monoid (Monoid(..), (<>))
import Data.Ratio (Ratio)
import Data.Typeable (Typeable(..))
import GHC.Generics

import Unbound.Generics.LocallyNameless.Name

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
data AlphaCtx = AlphaCtx { ctxMode :: Mode }

data Mode = Term | Pat

initialCtx :: AlphaCtx
initialCtx = AlphaCtx { ctxMode = Term }

-- | A @DisjointSet a@ is a 'Just' a list of distinct @a@s.  In addition to a monoidal
-- structure, a disjoint set also has an annihilator 'inconsistentDisjointSet'.
--
-- @@
--   inconsistentDisjointSet <> s == inconsistentDisjointSet
--   s <> inconsistentDisjoinSet == inconsistentDisjointSet
-- @@
newtype DisjointSet a = DisjointSet (Maybe [a])

instance Eq a => Monoid (DisjointSet a) where
  mempty = DisjointSet (Just [])
  mappend s1 s2 =
    case (s1, s2) of
      (DisjointSet (Just xs), DisjointSet (Just ys)) | disjointLists xs ys -> DisjointSet (Just (xs <> ys))
      _ -> inconsistentDisjointSet

instance Foldable DisjointSet where
  foldMap summarize (DisjointSet ms) = foldMap (foldMap summarize) ms

inconsistentDisjointSet :: DisjointSet a
inconsistentDisjointSet = DisjointSet Nothing

singletonDisjointSet :: a -> DisjointSet a
singletonDisjointSet x = DisjointSet (Just [x])

disjointLists :: Eq a => [a] -> [a] -> Bool
disjointLists xs ys = null (intersect xs ys)

isConsistentDisjointSet :: DisjointSet a -> Bool
isConsistentDisjointSet (DisjointSet Nothing) = False
isConsistentDisjointSet _ = True

-- | Types that are instances of @Alpha@ may participate in name representation.
--
-- Minimal instance is entirely empty, provided that your type is an instance of
-- 'Generic'.
class (Show a) => Alpha a where
  -- | See 'aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = (gaeq c) `on` from

  close :: Alpha b => AlphaCtx -> b -> a -> a
  default close :: (Generic a, GAlpha (Rep a), Alpha b) => AlphaCtx -> b -> a -> a
  close c b = to . gclose c b . from

  open :: Alpha b => AlphaCtx -> b -> a -> a
  default open :: (Generic a, GAlpha (Rep a), Alpha b) => AlphaCtx -> b -> a -> a
  open c b = to . gopen c b . from

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid pattern.
  isPat :: a -> DisjointSet AnyName
  default isPat :: (Generic a, GAlpha (Rep a)) => a -> DisjointSet AnyName
  isPat = gisPat . from
  
  -- | @isEmbed@ is needed internally for the implementation of
  --   'isPat'.  @isEmbed@ is true for terms wrapped in 'Embed' and zero
  --   or more occurrences of 'Shift'.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False

-- | The "Generic" representation version of 'Alpha'
class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool
  gclose :: Alpha b => AlphaCtx -> b -> f a -> f a
  gopen :: Alpha b => AlphaCtx -> b -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName

instance (Alpha c) => GAlpha (K1 i c) where
  gaeq ctx (K1 c1) (K1 c2) = aeq' ctx c1 c2

  gclose ctx b = K1 . close ctx b . unK1
  gopen ctx b = K1 . open ctx b . unK1

  gisPat = isPat . unK1

instance GAlpha f => GAlpha (M1 i c f) where
  gaeq ctx (M1 f1) (M1 f2) = gaeq ctx f1 f2

  gclose ctx b = M1 . gclose ctx b . unM1
  gopen ctx b = M1 . gclose ctx b . unM1

  gisPat = gisPat . unM1

instance GAlpha U1 where
  gaeq _ctx _ _ = True

  gclose _ctx _b _ = U1
  gopen _ctx _b _ = U1

  gisPat _ = mempty

instance GAlpha V1 where
  gaeq _ctx _ _ = False

  gclose _ctx _b _ = undefined
  gopen _ctx _b _ = undefined

  gisPat _ = mempty

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gaeq ctx (f1 :*: g1) (f2 :*: g2) =
    gaeq ctx f1 f2 && gaeq ctx g1 g2

  gclose ctx b (f :*: g) = gclose ctx b f :*: gclose ctx b g
  gopen ctx b (f :*: g) = gopen ctx b f :*: gopen ctx b g

  gisPat (f :*: g) = gisPat f <> gisPat g

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gaeq ctx  (L1 f1) (L1 f2) = gaeq ctx f1 f2
  gaeq ctx  (R1 g1) (R1 g2) = gaeq ctx g1 g2
  gaeq _ctx _       _       = False

  gclose ctx b (L1 f) = L1 (gclose ctx b f)
  gclose ctx b (R1 g) = R1 (gclose ctx b g)
  gopen ctx b (L1 f) = L1 (gopen ctx b f)
  gopen ctx b (R1 g) = R1 (gopen ctx b g)

  gisPat (L1 f) = gisPat f
  gisPat (R1 g) = gisPat g

-- ============================================================
-- Alpha instances for the usual types

instance Alpha Int where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance Alpha Char where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance Alpha Integer where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance Alpha Float where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance Alpha Double where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance (Integral n, Alpha n) => Alpha (Ratio n) where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

instance Alpha a => Alpha (Maybe a)
instance Alpha a => Alpha [a]
instance (Alpha a,Alpha b) => Alpha (Either a b)
instance (Alpha a,Alpha b) => Alpha (a,b)
instance (Alpha a,Alpha b,Alpha c) => Alpha (a,b,c)
instance (Alpha a, Alpha b,Alpha c, Alpha d) => Alpha (a,b,c,d)
instance (Alpha a, Alpha b,Alpha c, Alpha d, Alpha e) =>
   Alpha (a,b,c,d,e)

-- ============================================================
-- Alpha instances for interesting types

instance Typeable a => Alpha (Name a) where
  aeq' ctx n1 n2 =
    case ctxMode ctx of
      Term -> n1 == n2 -- in terms, better be the same name
      Pat  -> True     -- in a pattern, names are always equivlent
                       -- (since they're both bound, so they can
                       -- vary).

  close _ _ _ = error "unimplemented: close for Name"
  open _ _ _ = error "unimplemented: open for Name"
  

  isPat n = if isFreeName n
            then singletonDisjointSet (AnyName n)
            else inconsistentDisjointSet

