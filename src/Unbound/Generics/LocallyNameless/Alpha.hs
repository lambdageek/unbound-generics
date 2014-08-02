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
import Data.Typeable (Typeable(..), gcast)
import GHC.Generics

import Unbound.Generics.LocallyNameless.Name

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
--
-- The context records whether we are currently operating on terms or patterns,
-- and how many binding levels we've descended.
data AlphaCtx = AlphaCtx { ctxMode :: !Mode, ctxLevel :: !Integer }

data Mode = Term | Pat
          deriving Eq

initialCtx :: AlphaCtx
initialCtx = AlphaCtx { ctxMode = Term, ctxLevel = 0 }

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
  -- | See 'Unbound.Generics.LocallyNameless.Operations.aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = (gaeq c) `on` from

  -- | Replace free names by bound names.
  close :: Alpha b => AlphaCtx -> b -> a -> a
  default close :: (Generic a, GAlpha (Rep a), Alpha b) => AlphaCtx -> b -> a -> a
  close c b = to . gclose c b . from

  -- | Replace bound names by free names.
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

  -- | If @a@ is a pattern, finds the @n@th name in the pattern
  -- (starting from zero), returning the number of names encountered
  -- in not found.
  nthPatFind :: a -> NthPatFind
  default nthPatFind :: (Generic a, GAlpha (Rep a)) => a -> NthPatFind
  nthPatFind = gnthPatFind . from

  -- | If @a@ is a pattern, find the index of the given name in the pattern.
  namePatFind :: a -> NamePatFind
  default namePatFind :: (Generic a, GAlpha (Rep a)) => a -> NamePatFind
  namePatFind = gnamePatFind . from

type NthPatFind = Integer -> Either Integer AnyName
type NamePatFind = AnyName -> Either Integer Integer -- Left - names skipped over
                                                     -- Right - index of the name we found

-- | The "Generic" representation version of 'Alpha'
class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool
  gclose :: Alpha b => AlphaCtx -> b -> f a -> f a
  gopen :: Alpha b => AlphaCtx -> b -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName

  gnthPatFind :: f a -> NthPatFind
  gnamePatFind :: f a -> NamePatFind

instance (Alpha c) => GAlpha (K1 i c) where
  gaeq ctx (K1 c1) (K1 c2) = aeq' ctx c1 c2

  gclose ctx b = K1 . close ctx b . unK1
  gopen ctx b = K1 . open ctx b . unK1

  gisPat = isPat . unK1

  gnthPatFind = nthPatFind . unK1
  gnamePatFind = namePatFind . unK1

instance GAlpha f => GAlpha (M1 i c f) where
  gaeq ctx (M1 f1) (M1 f2) = gaeq ctx f1 f2

  gclose ctx b = M1 . gclose ctx b . unM1
  gopen ctx b = M1 . gclose ctx b . unM1

  gisPat = gisPat . unM1

  gnthPatFind = gnthPatFind . unM1
  gnamePatFind = gnamePatFind . unM1
  
instance GAlpha U1 where
  gaeq _ctx _ _ = True

  gclose _ctx _b _ = U1
  gopen _ctx _b _ = U1

  gisPat _ = mempty

  gnthPatFind _ _i = Left 0
  gnamePatFind _ _ = Left 0

instance GAlpha V1 where
  gaeq _ctx _ _ = False

  gclose _ctx _b _ = undefined
  gopen _ctx _b _ = undefined

  gisPat _ = mempty

  gnthPatFind _ _i = Left 0
  gnamePatFind _ _ = Left 0

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gaeq ctx (f1 :*: g1) (f2 :*: g2) =
    gaeq ctx f1 f2 && gaeq ctx g1 g2

  gclose ctx b (f :*: g) = gclose ctx b f :*: gclose ctx b g
  gopen ctx b (f :*: g) = gopen ctx b f :*: gopen ctx b g

  gisPat (f :*: g) = gisPat f <> gisPat g

  gnthPatFind (f :*: g) i = case gnthPatFind f i of
    Left i' -> gnthPatFind g i'
    Right ans -> Right ans
  gnamePatFind (f :*: g) n = case gnamePatFind f n of
    Left j -> case gnamePatFind g n of
      Left i -> Left $! j + i
      Right k -> Right $! j + k
    Right k -> Right k

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

  gnthPatFind (L1 f) i = gnthPatFind f i
  gnthPatFind (R1 g) i = gnthPatFind g i
  
  gnamePatFind (L1 f) n = gnamePatFind f n
  gnamePatFind (R1 g) n = gnamePatFind g n

-- ============================================================
-- Alpha instances for the usual types

instance Alpha Int where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

instance Alpha Char where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

instance Alpha Integer where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

instance Alpha Float where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

instance Alpha Double where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

instance (Integral n, Alpha n) => Alpha (Ratio n) where
  aeq' _ctx i j = i == j

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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

  open ctx b a@(Bn l k) =
    if ctxMode ctx == Term && ctxLevel ctx == l
    then case nthPatFind b k of
      Right (AnyName nm) -> case gcast nm of
        Just nm' -> nm'
        Nothing -> error "LocallyNameless.open: inconsistent sorts"
      Left _ -> error "LocallyNameless.open : inconsistency - pattern had too few variables"
    else
      a
  open _ctx _ a = a

  close ctx b a@(Fn _ _) =
    if ctxMode ctx == Term
    then case namePatFind b (AnyName a) of
      Right k -> Bn (ctxLevel ctx) k
      Left _ -> a
    else a
  close _ctx _ a = a
  

  isPat n = if isFreeName n
            then singletonDisjointSet (AnyName n)
            else inconsistentDisjointSet

  nthPatFind nm i =
    if i == 0 then Right (AnyName nm) else Left $! i-1

  namePatFind nm1 (AnyName nm2) =
    case gcast nm1 of
      Just nm1' -> if nm1' == nm2 then Right 0 else Left 1
      Nothing -> Left 1
