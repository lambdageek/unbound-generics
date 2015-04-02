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
  -- * Implementation details
  , NthPatFind
  , NamePatFind
  , AlphaCtx
  , initialCtx
  , patternCtx
  , termCtx
  , isTermCtx
  , incrLevelCtx
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
  ) where

import Control.Applicative (Applicative(..), (<$>))
import Control.Arrow (first)
import Control.Monad (liftM)
import Data.Function (on)
import Data.Functor.Contravariant (Contravariant(..))
import Data.Foldable (Foldable(..))
import Data.List (intersect)
import Data.Monoid (Monoid(..), (<>))
import Data.Ratio (Ratio)
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

-- | A @DisjointSet a@ is a 'Just' a list of distinct @a@s.  In addition to a monoidal
-- structure, a disjoint set also has an annihilator 'inconsistentDisjointSet'.
--
-- @
--   inconsistentDisjointSet \<> s == inconsistentDisjointSet
--   s \<> inconsistentDisjoinSet == inconsistentDisjointSet
-- @
newtype DisjointSet a = DisjointSet (Maybe [a])

instance Eq a => Monoid (DisjointSet a) where
  mempty = DisjointSet (Just [])
  mappend s1 s2 =
    case (s1, s2) of
      (DisjointSet (Just xs), DisjointSet (Just ys)) | disjointLists xs ys -> DisjointSet (Just (xs <> ys))
      _ -> inconsistentDisjointSet

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

-- | Types that are instances of @Alpha@ may participate in name representation.
--
-- Minimal instance is entirely empty, provided that your type is an instance of
-- 'Generic'.
class (Show a) => Alpha a where
  -- | See 'Unbound.Generics.LocallyNameless.Operations.aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  default aeq' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> a -> a -> Bool
  aeq' c = (gaeq c) `on` from

  -- | See 'Unbound.Generics.LocallyNameless.Operations.fvAny'.
  --
  -- @
  --  fvAny' :: Fold a AnyName
  -- @
  fvAny' :: (Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  default fvAny' :: (Generic a, GAlpha (Rep a), Contravariant f, Applicative f) => AlphaCtx -> (AnyName -> f AnyName) -> a -> f a
  fvAny' c nfn = fmap to . gfvAny c nfn . from

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

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid term.
  isTerm :: a -> Bool
  default isTerm :: (Generic a, GAlpha (Rep a)) => a -> Bool
  isTerm = gisTerm . from

  -- | @isEmbed@ is needed internally for the implementation of
  --   'isPat'.  @isEmbed@ is true for terms wrapped in 'Embed' and zero
  --   or more occurrences of 'Shift'.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False

  -- | If @a@ is a pattern, finds the @n@th name in the pattern
  -- (starting from zero), returning the number of names encountered
  -- if not found.
  nthPatFind :: a -> NthPatFind
  default nthPatFind :: (Generic a, GAlpha (Rep a)) => a -> NthPatFind
  nthPatFind = gnthPatFind . from

  -- | If @a@ is a pattern, find the index of the given name in the pattern.
  namePatFind :: a -> NamePatFind
  default namePatFind :: (Generic a, GAlpha (Rep a)) => a -> NamePatFind
  namePatFind = gnamePatFind . from

  -- | See 'Unbound.Generics.LocallyNameless.Operations.swaps'. Apply
  -- the given permutation of variable names to the given pattern.
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  default swaps' :: (Generic a, GAlpha (Rep a)) => AlphaCtx -> Perm AnyName -> a -> a
  swaps' ctx perm = to . gswaps ctx perm . from

  -- | See 'Unbound.Generics.LocallyNameless.Operations.freshen'.
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  default lfreshen' :: (LFresh m, Generic a, GAlpha (Rep a))
                       => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  lfreshen' ctx m cont = glfreshen ctx (from m) (cont . to)

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

instance Applicative (FFM f) where
  pure = return
  (FFM h) <*> (FFM k) = FFM (\r j -> h (\f -> k (r . f) j) j)

instance Monad (FFM f) where
  return x = FFM (\r _j -> r x)
  (FFM h) >>= f = FFM (\r j -> h (\x -> runFFM (f x) r j) j)

instance Fresh m => Fresh (FFM m) where
  fresh = liftFFM . fresh 

liftFFM :: Monad m => m a -> FFM m a
liftFFM m = FFM (\r j -> j (liftM r m))

retractFFM :: Monad m => FFM m a -> m a
retractFFM (FFM h) = h return j
  where
    j mmf = mmf >>= \mf -> mf

-- | The result of @'nthPatFind' a i@ is @Left k@ where @k@ is the
-- number of names in pattern @a@ with @k < i@ or @Right x@ where @x@
-- is the @i@th name in @a@
type NthPatFind = Integer -> Either Integer AnyName

-- | The result of @'namePatFind' a x@ is either @Left i@ if @a@ is a pattern that
-- contains @i@ free names none of which are @x@, or @Right j@ if @x@ is the @j@th name
-- in @a@
type NamePatFind = AnyName -> Either Integer Integer -- Left - names skipped over
                                                     -- Right - index of the name we found

-- | The "Generic" representation version of 'Alpha'
class GAlpha f where
  gaeq :: AlphaCtx -> f a -> f a -> Bool

  gfvAny :: (Contravariant g, Applicative g) => AlphaCtx -> (AnyName -> g AnyName) -> f a -> g (f a)

  gclose :: Alpha b => AlphaCtx -> b -> f a -> f a
  gopen :: Alpha b => AlphaCtx -> b -> f a -> f a

  gisPat :: f a -> DisjointSet AnyName
  gisTerm :: f a -> Bool

  gnthPatFind :: f a -> NthPatFind
  gnamePatFind :: f a -> NamePatFind

  gswaps :: AlphaCtx -> Perm AnyName -> f a -> f a
  gfreshen :: Fresh m => AlphaCtx -> f a -> FFM m (f a, Perm AnyName)

  glfreshen :: LFresh m => AlphaCtx -> f a -> (f a -> Perm AnyName -> m b) -> m b

  gacompare :: AlphaCtx -> f a -> f a -> Ordering

instance (Alpha c) => GAlpha (K1 i c) where
  gaeq ctx (K1 c1) (K1 c2) = aeq' ctx c1 c2

  gfvAny ctx nfn = fmap K1 . fvAny' ctx nfn . unK1

  gclose ctx b = K1 . close ctx b . unK1
  gopen ctx b = K1 . open ctx b . unK1

  gisPat = isPat . unK1
  gisTerm = isTerm . unK1

  gnthPatFind = nthPatFind . unK1
  gnamePatFind = namePatFind . unK1

  gswaps ctx perm = K1 . swaps' ctx perm . unK1
  gfreshen ctx = liftM (first K1) . liftFFM . freshen' ctx . unK1

  glfreshen ctx (K1 c) cont = lfreshen' ctx c (cont . K1)

  gacompare ctx (K1 c1) (K1 c2) = acompare' ctx c1 c2

instance GAlpha f => GAlpha (M1 i c f) where
  gaeq ctx (M1 f1) (M1 f2) = gaeq ctx f1 f2

  gfvAny ctx nfn = fmap M1 . gfvAny ctx nfn . unM1

  gclose ctx b = M1 . gclose ctx b . unM1
  gopen ctx b = M1 . gopen ctx b . unM1

  gisPat = gisPat . unM1
  gisTerm = gisTerm . unM1

  gnthPatFind = gnthPatFind . unM1
  gnamePatFind = gnamePatFind . unM1

  gswaps ctx perm = M1 . gswaps ctx perm . unM1
  gfreshen ctx = liftM (first M1) . gfreshen ctx . unM1

  glfreshen ctx (M1 f) cont =
    glfreshen ctx f (cont . M1)

  gacompare ctx (M1 f1) (M1 f2) = gacompare ctx f1 f2

instance GAlpha U1 where
  gaeq _ctx _ _ = True

  gfvAny _ctx _nfn _ = pure U1

  gclose _ctx _b _ = U1
  gopen _ctx _b _ = U1

  gisPat _ = mempty
  gisTerm _ = True

  gnthPatFind _ = Left
  gnamePatFind _ _ = Left 0

  gswaps _ctx _perm _ = U1
  gfreshen _ctx _ = return (U1, mempty)

  glfreshen _ctx _ cont = cont U1 mempty

  gacompare _ctx _ _ = EQ

instance GAlpha V1 where
  gaeq _ctx _ _ = False

  gfvAny _ctx _nfn = pure

  gclose _ctx _b _ = undefined
  gopen _ctx _b _ = undefined

  gisPat _ = mempty
  gisTerm _ = False

  gnthPatFind _ = Left
  gnamePatFind _ _ = Left 0

  gswaps _ctx _perm _ = undefined
  gfreshen _ctx _ = return (undefined, mempty)

  glfreshen _ctx _ cont = cont undefined mempty

  gacompare _ctx _ _ = error "LocallyNameless.gacompare: undefined for empty data types"

instance (GAlpha f, GAlpha g) => GAlpha (f :*: g) where
  gaeq ctx (f1 :*: g1) (f2 :*: g2) =
    gaeq ctx f1 f2 && gaeq ctx g1 g2

  gfvAny ctx nfn (f :*: g) = (:*:) <$> gfvAny ctx nfn f
                                   <*> gfvAny ctx nfn g

  gclose ctx b (f :*: g) = gclose ctx b f :*: gclose ctx b g
  gopen ctx b (f :*: g) = gopen ctx b f :*: gopen ctx b g

  gisPat (f :*: g) = gisPat f <> gisPat g
  gisTerm (f :*: g) = gisTerm f && gisTerm g

  gnthPatFind (f :*: g) i = case gnthPatFind f i of
    Left i' -> gnthPatFind g i'
    Right ans -> Right ans
  gnamePatFind (f :*: g) n = case gnamePatFind f n of
    Left j -> case gnamePatFind g n of
      Left i -> Left $! j + i
      Right k -> Right $! j + k
    Right k -> Right k

  gswaps ctx perm (f :*: g) =
    gswaps ctx perm f :*: gswaps ctx perm g

  gfreshen ctx (f :*: g) = do
    ~(g', perm2) <- gfreshen ctx g
    ~(f', perm1) <- gfreshen ctx (gswaps ctx perm2 f)
    return (f' :*: g', perm1 <> perm2)

  glfreshen ctx (f :*: g) cont =
    glfreshen ctx g $ \g' perm2 ->
    glfreshen ctx (gswaps ctx perm2 f) $ \f' perm1 ->
    cont (f' :*: g') (perm1 <> perm2)

  gacompare ctx (f1 :*: g1) (f2 :*: g2) =
    (gacompare ctx f1 f2) <> (gacompare ctx g1 g2)

instance (GAlpha f, GAlpha g) => GAlpha (f :+: g) where
  gaeq ctx  (L1 f1) (L1 f2) = gaeq ctx f1 f2
  gaeq ctx  (R1 g1) (R1 g2) = gaeq ctx g1 g2
  gaeq _ctx _       _       = False

  gfvAny ctx nfn (L1 f) = fmap L1 (gfvAny ctx nfn f)
  gfvAny ctx nfn (R1 g) = fmap R1 (gfvAny ctx nfn g)

  gclose ctx b (L1 f) = L1 (gclose ctx b f)
  gclose ctx b (R1 g) = R1 (gclose ctx b g)
  gopen ctx b (L1 f) = L1 (gopen ctx b f)
  gopen ctx b (R1 g) = R1 (gopen ctx b g)

  gisPat (L1 f) = gisPat f
  gisPat (R1 g) = gisPat g

  gisTerm (L1 f) = gisTerm f
  gisTerm (R1 g) = gisTerm g

  gnthPatFind (L1 f) i = gnthPatFind f i
  gnthPatFind (R1 g) i = gnthPatFind g i
  
  gnamePatFind (L1 f) n = gnamePatFind f n
  gnamePatFind (R1 g) n = gnamePatFind g n

  gswaps ctx perm (L1 f) = L1 (gswaps ctx perm f)
  gswaps ctx perm (R1 f) = R1 (gswaps ctx perm f)

  gfreshen ctx (L1 f) = liftM (first L1) (gfreshen ctx f)
  gfreshen ctx (R1 f) = liftM (first R1) (gfreshen ctx f)
  
  glfreshen ctx (L1 f) cont =
    glfreshen ctx f (cont . L1)
  glfreshen ctx (R1 g) cont =
    glfreshen ctx g (cont . R1)

  gacompare _ctx (L1 _) (R1 _)   = LT
  gacompare _ctx (R1 _) (L1 _)   = GT
  gacompare ctx  (L1 f1) (L1 f2) = gacompare ctx f1 f2
  gacompare ctx  (R1 g1) (R1 g2) = gacompare ctx g1 g2

-- ============================================================
-- Alpha instances for the usual types

instance Alpha Int where
  aeq' _ctx i j = i == j

  fvAny' _ctx _nfn i = pure i

  close _ctx _b i = i
  open _ctx _b i = i

  isPat _ = mempty
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

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
  isTerm _ = True

  nthPatFind _ = Left
  namePatFind _ _ = Left 0

  swaps' _ctx _p i = i
  freshen' _ctx i = return (i, mempty)
  lfreshen' _ctx i cont = cont i mempty

  acompare' _ctx i j = compare i j

instance Alpha Bool

instance Alpha a => Alpha (Maybe a)
instance Alpha a => Alpha [a]
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
    then case nthPatFind b k of
      Right (AnyName nm) -> case gcast nm of
        Just nm' -> nm'
        Nothing -> error "LocallyNameless.open: inconsistent sorts"
      Left _ -> error "LocallyNameless.open : inconsistency - pattern had too few variables"
    else
      a
  open _ctx _ a = a

  close ctx b a@(Fn _ _) =
    if isTermCtx ctx
    then case namePatFind b (AnyName a) of
      Right k -> Bn (ctxLevel ctx) k
      Left _ -> a
    else a
  close _ctx _ a = a
  

  isPat n = if isFreeName n
            then singletonDisjointSet (AnyName n)
            else inconsistentDisjointSet

  isTerm _ = True

  nthPatFind nm i =
    if i == 0 then Right (AnyName nm) else Left $! i-1

  namePatFind nm1 (AnyName nm2) =
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

  isTerm _ = True

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
    
  nthPatFind nm i =
    if i == 0 then Right nm else Left $! i - 1

  namePatFind nmHave nmWant =
    if nmHave == nmWant
    then Right 0
    else Left 1

  acompare' _ x y | x == y = EQ

  acompare' ctx (AnyName n1) (AnyName n2)
    | isTermCtx ctx =
      case compare (typeOf n1) (typeOf n2) of
        EQ -> case gcast n2 of
          Just n2' -> acompare' ctx n1 n2'
          Nothing -> error "LocallyNameless.acompare': Equal type representations, but gcast failed in comparing two AnyName values"
        ord -> ord

  acompare' _ _ _ = EQ
