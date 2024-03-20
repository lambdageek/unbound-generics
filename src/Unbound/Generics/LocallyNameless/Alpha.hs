{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.Alpha
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Use the 'Alpha' typeclass to mark types that may contain 'Name's.
{-# LANGUAGE DefaultSignatures
             , FlexibleContexts
             , TypeOperators
             , RankNTypes
  #-}
module Unbound.Generics.LocallyNameless.Alpha (
  -- * Name-aware opertions
  Alpha(..)
  -- * Binder variables
  , DisjointSet(..)
  , inconsistentDisjointSet
  , singletonDisjointSet
  , isConsistentDisjointSet
  , isNullDisjointSet
  -- * Implementation details
  , NthPatFind(..)
  , NamePatFind(..)
  , AlphaCtx
  , ctxLevel
  , initialCtx
  , patternCtx
  , termCtx
  , isTermCtx
  , incrLevelCtx
  , decrLevelCtx
  , isZeroLevelCtx
  , ctxLevel
  -- * Internal
  , gaeq
  , gfvAny
  , gclose
  , gopen
  , gisPat
  , gisTerm
  , gnthPatFind
  , gnamePatFind
  , gswaps
  , gfreshen
  , glfreshen
  , gacompare
    -- ** Interal helpers for gfreshen
  , FFM
  , liftFFM
  , retractFFM
  ) where

import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow (first)
import Control.Monad (liftM)
import Data.Function (on)
import Data.Functor.Contravariant (Contravariant(..))
import Data.Foldable (Foldable(..))
import Data.List (intersect)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (Monoid(..), All(..))
import Data.Ratio (Ratio)
import Data.Semigroup as Sem
import Data.Typeable (Typeable, gcast, typeOf)
import GHC.Generics

import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.PermM

-- | Some 'Alpha' operations need to record information about their
-- progress.  Instances should just pass it through unchanged.
--
-- The context records whether we are currently operating on terms or patterns,
-- and how many binding levels we've descended.
data AlphaCtx = AlphaCtx { ctxMode :: !Mode, ctxLevel :: !Integer }

data Mode = Term | Pat
          deriving Eq

-- | The starting context for alpha operations: we are expecting to
-- work on terms and we are under no binders.
initialCtx :: AlphaCtx
initialCtx = AlphaCtx { ctxMode = Term, ctxLevel = 0 }

-- | Switches to a context where we expect to operate on patterns.
patternCtx :: AlphaCtx -> AlphaCtx
patternCtx ctx = ctx { ctxMode = Pat }

-- | Switches to a context where we expect to operate on terms.
termCtx :: AlphaCtx -> AlphaCtx
termCtx ctx = ctx { ctxMode = Term }

-- | Returns 'True' iff we are in a context where we expect to see terms.
isTermCtx :: AlphaCtx -> Bool
isTermCtx (AlphaCtx {ctxMode = Term}) = True
isTermCtx _                           = False

-- | Increment the number of binders that we are operating under.
incrLevelCtx :: AlphaCtx -> AlphaCtx
incrLevelCtx ctx = ctx { ctxLevel = 1 + ctxLevel ctx }

-- | Decrement the number of binders that we are operating under.
decrLevelCtx :: AlphaCtx -> AlphaCtx
decrLevelCtx ctx = ctx { ctxLevel = ctxLevel ctx - 1 }

-- | Are we operating under no binders?
isZeroLevelCtx :: AlphaCtx -> Bool
isZeroLevelCtx ctx = ctxLevel ctx == 0

-- | A @DisjointSet a@ is a 'Just' a list of distinct @a@s.  In addition to a monoidal
-- structure, a disjoint set also has an annihilator 'inconsistentDisjointSet'.
--
-- @
--   inconsistentDisjointSet \<> s == inconsistentDisjointSet
--   s \<> inconsistentDisjoinSet == inconsistentDisjointSet
-- @
newtype DisjointSet a = DisjointSet (Maybe [a])

-- | @since 0.3.2
instance Eq a => Sem.Semigroup (DisjointSet a) where
  (<>) = \s1 s2 ->
    case (s1, s2) of
      (DisjointSet (Just xs), DisjointSet (Just ys)) | disjointLists xs ys -> DisjointSet (Just (xs <> ys))
      _ -> inconsistentDisjointSet

instance Eq a => Monoid (DisjointSet a) where
  mempty = DisjointSet (Just [])
  mappend = (<>)

instance Foldable DisjointSet where
  foldMap summarize (DisjointSet ms) = foldMap (foldMap summarize) ms

-- | Returns a @DisjointSet a@ that is the annihilator element for the 'Monoid' instance of 'DisjointSet'.
inconsistentDisjointSet :: DisjointSet a
inconsistentDisjointSet = DisjointSet Nothing

-- | @singletonDisjointSet x@ a @DisjointSet a@ that contains the single element @x@
singletonDisjointSet :: a -> DisjointSet a
singletonDisjointSet x = DisjointSet (Just [x])

disjointLists :: Eq a => [a] -> [a] -> Bool
disjointLists xs ys = null (intersect xs ys)

-- | @isConsistentDisjointSet@ returns @True@ iff the given disjoint set is not inconsistent.
isConsistentDisjointSet :: DisjointSet a -> Bool
isConsistentDisjointSet (DisjointSet Nothing) = False
isConsistentDisjointSet _ = True

-- | @isNullDisjointSet@ return @True@ iff the given disjoint set is 'mempty'.
isNullDisjointSet :: DisjointSet a -> Bool
isNullDisjointSet (DisjointSet (Just [])) = True
isNullDisjointSet _ = False

-- | Types that are instances of @Alpha@ may participate in name representation.
--
-- Minimal instance is entirely empty, provided that your type is an instance of
-- 'Generic'.
class (Show a) => Alpha a where
  -- | See 'Unbound.Generics.LocallyNameless.Operations.aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = (gaeq c) `on` from
  {-# INLINE aeq' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.fvAny'.
  --
  -- @
  --  fvAny' :: Fold a AnyName
  -- @
  fvAny' :: (Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  default fvAny' :: (Generic a, GAlpha (Rep a), Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  fvAny' c nfn = fmap to . gfvAny c nfn . from
  {-# INLINE fvAny' #-}

  -- | Replace free names by bound names.
  close :: AlphaCtx -> NamePatFind -> a -> a
  default close :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> NamePatFind -> a -> a
  close c b = to . gclose c b . from
  {-# INLINE close #-}

  -- | Replace bound names by free names.
  open :: AlphaCtx -> NthPatFind -> a -> a
  default open :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> NthPatFind -> a -> a
  open c b = to . gopen c b . from
  {-# INLINE open #-}

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid pattern.
  isPat :: a -> DisjointSet AnyName
  default isPat :: (Generic a, GAlpha (Rep a)) => a -> DisjointSet AnyName
  isPat = gisPat . from
  {-# INLINE isPat #-}

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid term.
  isTerm :: a -> All
  default isTerm :: (Generic a, GAlpha (Rep a)) => a -> All
  isTerm = gisTerm . from
  {-# INLINE isTerm #-}

  -- | @isEmbed@ is needed internally for the implementation of
  --   'isPat'.  @isEmbed@ is true for terms wrapped in 'Embed' and zero
  --   or more occurrences of 'Shift'.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False
  {-# INLINE isEmbed #-}

  -- | If @a@ is a pattern, finds the @n@th name in the pattern
  -- (starting from zero), returning the number of names encountered
  -- if not found.
  nthPatFind :: a -> NthPatFind
  default nthPatFind :: (Generic a, GAlpha (Rep a)) => a -> NthPatFind
  nthPatFind = gnthPatFind . from
  {-# INLINE nthPatFind #-}

  -- | If @a@ is a pattern, find the index of the given name in the pattern.
  namePatFind :: a -> NamePatFind
  default namePatFind :: (Generic a, GAlpha (Rep a)) => a -> NamePatFind
  namePatFind = gnamePatFind . from
  {-# INLINE namePatFind #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.swaps'. Apply
  -- the given permutation of variable names to the given pattern.
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  default swaps' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> Perm AnyName -> a -> a
  swaps' ctx perm = to . gswaps ctx perm . from
  {-# INLINE swaps' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.freshen'.
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  default lfreshen' :: (LFresh m, Generic a, GAlpha (Rep a))
                       => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  lfreshen' ctx m cont = glfreshen ctx (from m) (cont . to)
  {-# INLINE lfreshen' #-}

  -- | See 'Unbound.Generics.LocallyNameless.Operations.freshen'.  Rename the free variables
  -- in the given term to be distinct from all other names seen in the monad @m@.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  default freshen'  :: (Generic a, GAlpha (Rep a), Fresh m) => AlphaCtx -> a -> m (a, Perm AnyName)
  freshen' ctx = retractFFM . liftM (first to) . gfreshen ctx . from

  -- | See 'Unbound.Generics.LocallyNameless.Operations.acompare'. An alpha-respecting total order on terms involving binders.
  acompare' :: AlphaCtx -> a -> a -> Ordering
  default acompare' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Ordering
  acompare' c = (gacompare c) `on` from

-- Internal: the free monad over the Functor f.  Note that 'freshen''
-- has a monadic return type and moreover we have to thread the
-- permutation through the 'gfreshen' calls to crawl over the value
-- constructors.  Since we don't know anything about the monad @m@,
-- GHC can't help us.  But note that none of the code in the generic
-- 'gfreshen' instances actually makes use of the 'Fresh.fresh'
-- function; they just plumb the dictionary through to any 'K' nodes
-- that happen to contain a value of a type like 'Name' that does
-- actually freshen something.  So what we do is we actually make
-- gfreshen work not in the monad @m@, but in the monad @FFM m@ and
-- then use 'retractFFM' in the default 'Alpha' method to return back
-- down to @m@.  We don't really make use of the fact that 'FFM'
-- reassociates the binds of the underlying monad, but it doesn't hurt
-- anything.  Mostly what we care about is giving the inliner a chance
-- to eliminate most of the monadic plumbing.
newtype FFM f a = FFM { runFFM :: forall r . (a -> r) -> (f r -> r) -> r }

instance Functor (FFM f) where
  fmap f (FFM h) = FFM (\r j -> h (r . f) j)
  {-# INLINE fmap #-}

instance Applicative (FFM f) where
  pure x = FFM (\r _j -> r x)
  {-# INLINE pure #-}
  (FFM h) <*> (FFM k) = FFM (\r j -> h (\f -> k (r . f) j) j)
  {-# INLINE (<*>) #-}

instance Monad (FFM f) where
  return = pure
  {-# INLINE return #-}
  (FFM h) >>= f = FFM (\r j -> h (\x -> runFFM (f x) r j) j)
  {-# INLINE (>>=) #-}

instance Fresh m => Fresh (FFM m) where
  fresh = liftFFM . fresh 
  {-# INLINE fresh #-}

liftFFM :: Monad m => m a -> FFM m a
liftFFM m = FFM (\r j -> j (liftM r m))
{-# INLINE liftFFM #-}

retractFFM :: Monad m => FFM m a -> m a
retractFFM (FFM h) = h return j
  where
    j mmf = mmf >>= \mf -> mf
{-# INLINE retractFFM #-}

-- | The result of @'nthPatFind' a i@ is @Left k@ where @i-k@ is the
-- number of names in pattern @a@ (with @k < i@) or @Right x@ where @x@
-- is the @i@th name in @a@
newtype NthPatFind = NthPatFind { runNthPatFind :: Integer -> Either Integer AnyName }

-- | @since 0.3.2
instance Sem.Semigroup NthPatFind where
  (<>) = \(NthPatFind f) (NthPatFind g) ->
    NthPatFind $ \i -> case f i of
    Left i' -> g i'
    found@Right {} -> found

instance Monoid NthPatFind where
  mempty = NthPatFind Left
  mappend = (<>)

-- | The result of @'namePatFind' a x@ is either @Left i@ if @a@ is a pattern that
-- contains @i@ free names none of which are @x@, or @Right j@ if @x@ is the @j@th name
-- in @a@
newtype NamePatFind = NamePatFind { runNamePatFind :: AnyName
                                                      -- Left - names skipped over
                                                      -- Right - index of the name we found
                                                      -> Either Integer Integer }

-- | @since 0.3.2
instance Sem.Semigroup NamePatFind where
  (<>) = \(NamePatFind f) (NamePatFind g) ->
    NamePatFind $ \nm -> case f nm of
    ans@Right {} -> ans
    Left n -> case g nm of
      Left m -> Left $! n + m
      Right i -> Right $! n + i

instance Monoid NamePatFind where
  mempty = NamePatFind (\_ -> Left 0)
  mappend = (<>)

-- | The "Generic" representation version of 'Alpha'
class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool

  gfvAny :: (Contravariant g, Applicative g) => AlphaCtx -> (AnyName -> g AnyName) -> f a -> g (f a)

  gclose :: AlphaCtx -> NamePatFind -> f a -> f a
  gopen :: AlphaCtx -> NthPatFind -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName
  gisTerm :: f a -> All

  gnthPatFind :: f a -> NthPatFind
  gnamePatFind :: f a -> NamePatFind

  gswaps :: AlphaCtx -> Perm AnyName -> f a -> f a
  gfreshen :: Fresh m => AlphaCtx -> f a -> FFM m (f a, Perm AnyName)

  glfreshen :: LFresh m => AlphaCtx -> f a -> (f a -> Perm AnyName -> m b) -> m b

  gacompare :: AlphaCtx -> f a -> f a -> Ordering

instance (Alpha c) => GAlpha (K1 i c) where
  gaeq ctx (K1 c1) (K1 c2) = aeq' ctx c1 c2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn = fmap K1 . fvAny' ctx nfn . unK1
  {-# INLINE gfvAny #-}
  
  gclose ctx b = K1 . close ctx b . unK1
  {-# INLINE gclose #-}
  gopen ctx b = K1 . open ctx b . unK1
  {-# INLINE gopen #-}

  gisPat = isPat . unK1
  {-# INLINE gisPat #-}
  gisTerm = isTerm . unK1
  {-# INLINE gisTerm #-}

  gnthPatFind = nthPatFind . unK1
  {-# INLINE gnthPatFind #-}
  gnamePatFind = namePatFind . unK1
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm = K1 . swaps' ctx perm . unK1
  {-# INLINE gswaps #-}
  gfreshen ctx = liftM (first K1) . liftFFM . freshen' ctx . unK1
  {-# INLINE gfreshen #-}

  glfreshen ctx (K1 c) cont = lfreshen' ctx c (cont . K1)
  {-# INLINE glfreshen #-}

  gacompare ctx (K1 c1) (K1 c2) = acompare' ctx c1 c2

instance GAlpha f => GAlpha (M1 i c f) where
  gaeq ctx (M1 f1) (M1 f2) = gaeq ctx f1 f2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn = fmap M1 . gfvAny ctx nfn . unM1
  {-# INLINE gfvAny #-}

  gclose ctx b = M1 . gclose ctx b . unM1
  {-# INLINE gclose #-}
  gopen ctx b = M1 . gopen ctx b . unM1
  {-# INLINE gopen #-}

  gisPat = gisPat . unM1
  {-# INLINE gisPat #-}
  gisTerm = gisTerm . unM1
  {-# INLINE gisTerm #-}

  gnthPatFind = gnthPatFind . unM1
  {-# INLINE gnthPatFind #-}
  gnamePatFind = gnamePatFind . unM1
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm = M1 . gswaps ctx perm . unM1
  {-# INLINE gswaps #-}
  gfreshen ctx = liftM (first M1) . gfreshen ctx . unM1
  {-# INLINE gfreshen #-}

  glfreshen ctx (M1 f) cont =
    glfreshen ctx f (cont . M1)
  {-# INLINE glfreshen #-}

  gacompare ctx (M1 f1) (M1 f2) = gacompare ctx f1 f2

instance GAlpha U1 where
  gaeq _ctx _ _ = True
  {-# INLINE gaeq #-}

  gfvAny _ctx _nfn _ = pure U1

  gclose _ctx _b _ = U1
  gopen _ctx _b _ = U1

  gisPat _ = mempty
  gisTerm _ = mempty

  gnthPatFind _ = mempty
  gnamePatFind _ = mempty

  gswaps _ctx _perm _ = U1
  gfreshen _ctx _ = return (U1, mempty)
  {-# INLINE gfreshen #-}

  glfreshen _ctx _ cont = cont U1 mempty

  gacompare _ctx _ _ = EQ

instance GAlpha V1 where
  gaeq _ctx _ _ = False
  {-# INLINE gaeq #-}

  gfvAny _ctx _nfn = pure

  gclose _ctx _b _ = undefined
  gopen _ctx _b _ = undefined

  gisPat _ = mempty
  gisTerm _ = mempty

  gnthPatFind _ = mempty
  gnamePatFind _ = mempty

  gswaps _ctx _perm _ = undefined
  gfreshen _ctx _ = return (undefined, mempty)
  {-# INLINE gfreshen #-}

  glfreshen _ctx _ cont = cont undefined mempty

  gacompare _ctx _ _ = error "LocallyNameless.gacompare: undefined for empty data types"

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gaeq ctx (f1 :*: g1) (f2 :*: g2) =
    gaeq ctx f1 f2 && gaeq ctx g1 g2
  {-# INLINE gaeq #-}

  gfvAny ctx nfn (f :*: g) = (:*:) <$> gfvAny ctx nfn f
                                   <*> gfvAny ctx nfn g
  {-# INLINE gfvAny #-}

  gclose ctx b (f :*: g) = gclose ctx b f :*: gclose ctx b g
  {-# INLINE gclose #-}
  gopen ctx b (f :*: g) = gopen ctx b f :*: gopen ctx b g
  {-# INLINE gopen #-}

  gisPat (f :*: g) = gisPat f <> gisPat g
  {-# INLINE gisPat #-}
  gisTerm (f :*: g) = gisTerm f <> gisTerm g
  {-# INLINE gisTerm #-}

  gnthPatFind (f :*: g) = gnthPatFind f <> gnthPatFind g
  {-# INLINE gnthPatFind #-}
  gnamePatFind (f :*: g) = gnamePatFind f <> gnamePatFind g
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm (f :*: g) =
    gswaps ctx perm f :*: gswaps ctx perm g
  {-# INLINE gswaps #-}

  gfreshen ctx (f :*: g) = do
    ~(g', perm2) <- gfreshen ctx g
    ~(f', perm1) <- gfreshen ctx (gswaps ctx perm2 f)
    return (f' :*: g', perm1 <> perm2)
  {-# INLINE gfreshen #-}

  glfreshen ctx (f :*: g) cont =
    glfreshen ctx g $ \g' perm2 ->
    glfreshen ctx (gswaps ctx perm2 f) $ \f' perm1 ->
    cont (f' :*: g') (perm1 <> perm2)
  {-# INLINE glfreshen #-}

  gacompare ctx (f1 :*: g1) (f2 :*: g2) =
    (gacompare ctx f1 f2) <> (gacompare ctx g1 g2)

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gaeq ctx  (L1 f1) (L1 f2) = gaeq ctx f1 f2
  gaeq ctx  (R1 g1) (R1 g2) = gaeq ctx g1 g2
  gaeq _ctx _       _       = False
  {-# INLINE gaeq #-}

  gfvAny ctx nfn (L1 f) = fmap L1 (gfvAny ctx nfn f)
  gfvAny ctx nfn (R1 g) = fmap R1 (gfvAny ctx nfn g)
  {-# INLINE gfvAny #-}
  
  gclose ctx b (L1 f) = L1 (gclose ctx b f)
  gclose ctx b (R1 g) = R1 (gclose ctx b g)
  {-# INLINE gclose #-}
  gopen ctx b (L1 f) = L1 (gopen ctx b f)
  gopen ctx b (R1 g) = R1 (gopen ctx b g)
  {-# INLINE gopen #-}

  gisPat (L1 f) = gisPat f
  gisPat (R1 g) = gisPat g
  {-# INLINE gisPat #-}

  gisTerm (L1 f) = gisTerm f
  gisTerm (R1 g) = gisTerm g
  {-# INLINE gisTerm #-}

  gnthPatFind (L1 f) = gnthPatFind f
  gnthPatFind (R1 g) = gnthPatFind g
  {-# INLINE gnthPatFind #-}

  gnamePatFind (L1 f) = gnamePatFind f
  gnamePatFind (R1 g) = gnamePatFind g
  {-# INLINE gnamePatFind #-}

  gswaps ctx perm (L1 f) = L1 (gswaps ctx perm f)
  gswaps ctx perm (R1 f) = R1 (gswaps ctx perm f)
  {-# INLINE gswaps #-}

  gfreshen ctx (L1 f) = liftM (first L1) (gfreshen ctx f)
  gfreshen ctx (R1 f) = liftM (first R1) (gfreshen ctx f)
  {-# INLINE gfreshen #-}
  
  glfreshen ctx (L1 f) cont =
    glfreshen ctx f (cont . L1)
  glfreshen ctx (R1 g) cont =
    glfreshen ctx g (cont . R1)
  {-# INLINE glfreshen #-}

  gacompare _ctx (L1 _) (R1 _)   = LT
  gacompare _ctx (R1 _) (L1 _)   = GT
  gacompare ctx  (L1 f1) (L1 f2) = gacompare ctx f1 f2
  gacompare ctx  (R1 g1) (R1 g2) = gacompare ctx g1 g2
  {-# INLINE gacompare #-}

-- ============================================================
-- Alpha instances for the usual types

instance Alpha Int where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Char where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Integer where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Float where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Double where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance (Integral n, Alpha n) => Alpha (Ratio n) where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = mempty

  nthPatFind _ = mempty
  namePatFind _ = mempty

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Bool

instance Alpha a => Alpha (Maybe a)
instance Alpha a => Alpha [a]
instance Alpha a => Alpha (NonEmpty a)
instance Alpha ()
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
    if isTermCtx ctx
    then n1 == n2 -- in terms, better be the same name
    else True     -- in a pattern, names are always equivlent (since
                  -- they're both bound, so they can vary).

  fvAny' ctx nfn nm = if isTermCtx ctx && isFreeName nm
                      then contramap AnyName  (nfn (AnyName nm))
                      else pure nm

  open ctx b a@(Bn l k) =
    if ctxMode ctx == Term && ctxLevel ctx == l
    then case runNthPatFind b k of
      Right (AnyName nm) -> case gcast nm of
        Just nm' -> nm'
        Nothing -> error "LocallyNameless.open: inconsistent sorts"
      Left _ -> error "LocallyNameless.open : inconsistency - pattern had too few variables"
    else
      a
  open _ctx _ a = a

  close ctx b a@(Fn _ _) =
    if isTermCtx ctx
    then case runNamePatFind b (AnyName a) of
      Right k -> Bn (ctxLevel ctx) k
      Left _ -> a
    else a
  close _ctx _ a = a
  

  isPat n = if isFreeName n
            then singletonDisjointSet (AnyName n)
            else inconsistentDisjointSet

  isTerm _ = mempty

  nthPatFind nm = NthPatFind $ \i ->
    if i == 0 then Right (AnyName nm) else Left $! i-1

  namePatFind nm1 = NamePatFind $ \(AnyName nm2) ->
    case gcast nm1 of
      Just nm1' -> if nm1' == nm2 then Right 0 else Left 1
      Nothing -> Left 1

  swaps' ctx perm nm =
    if isTermCtx ctx
    then case apply perm (AnyName nm) of
      AnyName nm' ->
        case gcast nm' of
          Just nm'' -> nm''
          Nothing -> error "Internal error swaps' on a Name returned permuted name of wrong sort"
    else nm
      
  freshen' ctx nm =
    if not (isTermCtx ctx)
    then do
      nm' <- fresh nm
      return (nm', single (AnyName nm) (AnyName nm'))
    else error "freshen' on a Name in term position"

  lfreshen' ctx nm cont =
    if not (isTermCtx ctx)
    then do
      nm' <- lfresh nm
      avoid [AnyName nm'] $ cont nm' $ single (AnyName nm) (AnyName nm')
    else error "lfreshen' on a Name in term position"

  acompare' ctx (Fn s1 i1) (Fn s2 i2)
    | isTermCtx ctx = (compare s1 s2) <> (compare i1 i2)

  acompare' ctx n1@(Bn i1 j1) n2@(Bn i2 j2)
    | isTermCtx ctx = mconcat [ compare (typeOf n1) (typeOf n2)
                              , compare i1 i2
                              , compare j1 j2
                              ]

  acompare' ctx (Fn _ _) (Bn _ _) | isTermCtx ctx = LT
  acompare' ctx (Bn _ _) (Fn _ _) | isTermCtx ctx = GT

  acompare' _ _          _                        = EQ

instance Alpha AnyName where
  aeq' ctx x y =
    if x == y
    then True
    else
      -- in a term unequal variables are unequal, in a pattern it's
      -- ok.
      not (isTermCtx ctx)

  fvAny' ctx nfn n@(AnyName nm) = if isTermCtx ctx && isFreeName nm
                                  then nfn n
                                  else pure n

  isTerm _ = mempty

  isPat n@(AnyName nm) = if isFreeName nm
                         then singletonDisjointSet n
                         else inconsistentDisjointSet

  swaps' ctx perm n =
    if isTermCtx ctx
    then apply perm n
    else n

  freshen' ctx (AnyName nm) =
    if isTermCtx ctx
    then error "LocallyNameless.freshen' on AnyName in Term mode"
    else do
      nm' <- fresh nm
      return (AnyName nm', single (AnyName nm) (AnyName nm'))

  lfreshen' ctx (AnyName nm) cont =
    if isTermCtx ctx
    then error "LocallyNameless.lfreshen' on AnyName in Term mode"
    else do
      nm' <- lfresh nm
      avoid [AnyName nm'] $ cont (AnyName nm') $ single (AnyName nm) (AnyName nm')

  open ctx b (AnyName nm) = AnyName (open ctx b nm)

  close ctx b (AnyName nm) = AnyName (close ctx b nm)
    
  nthPatFind nm = NthPatFind $ \i ->
    if i == 0 then Right nm else Left $! i - 1

  namePatFind nmHave = NamePatFind $ \nmWant ->
    if nmHave == nmWant then Right 0 else Left 1

  acompare' _ x y | x == y = EQ

  acompare' ctx (AnyName n1) (AnyName n2)
    | isTermCtx ctx =
      case compare (typeOf n1) (typeOf n2) of
        EQ -> case gcast n2 of
          Just n2' -> acompare' ctx n1 n2'
          Nothing -> error "LocallyNameless.acompare': Equal type representations, but gcast failed in comparing two AnyName values"
        ord -> ord

  acompare' _ _ _ = EQ
