-- |
-- Module     : Unbound.Generics.LocallyNameless.Subst
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- A typeclass for types that may participate in capture-avoiding substitution
--
-- The minimal definition is empty, provided your type is an instance of 'GHC.Generics.Generic'
-- 
-- @
-- type Var = Name Factor
-- data Expr = SumOf [Summand]
--           deriving (Show, Generic)
-- data Summand = ProductOf [Factor]
--           deriving (Show, Generic)
-- instance Subst Var Expr
-- instance Subst Var Summand
-- @
-- 
-- The default instance just propagates the substitution into the constituent factors.
-- 
-- If you identify the variable occurrences by implementing the 'isvar' function, the derived 'subst' function
-- will be able to substitute a factor for a variable.
-- 
-- @
-- data Factor = V Var
--             | C Int
--             | Subexpr Expr
--           deriving (Show, Generic)
-- instance Subst Var Factor where
--   isvar (V v) = Just (SubstName v)
--   isvar _     = Nothing
-- @
--
{-# LANGUAGE DefaultSignatures
             , FlexibleContexts
             , FlexibleInstances
             , GADTs
             , MultiParamTypeClasses
             , ScopedTypeVariables
             , TypeOperators
 #-}
module Unbound.Generics.LocallyNameless.Subst (
  SubstName(..)
  , SubstCoerce(..)
  , Subst(..)
  , substBind
  , instantiate
  ) where

import GHC.Generics

import Data.List (find)
import Data.List.NonEmpty (NonEmpty)

import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Shift
import Unbound.Generics.LocallyNameless.Ignore
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Rebind
import Unbound.Generics.LocallyNameless.Rec
import Unbound.Generics.LocallyNameless.Internal.GSubst

-- | See 'isVar'
data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

-- | See 'isCoerceVar'
data SubstCoerce a b where
  SubstCoerce :: Name b -> (b -> Maybe a) -> SubstCoerce a b

-- | Immediately substitute for the bound variables of a pattern
-- in a binder, without first naming the variables.
-- NOTE: this operation does not check that the number of terms passed in
-- match the number of variables in the pattern. (Or that they are of appropriate type.)
instantiate :: (Alpha a, Alpha b, Alpha p , Subst a b) => Bind p b -> [a] -> b
instantiate bnd u = instantiate_ bnd u

-- | A version of 'instantiate' with a more general type
instantiate_ :: Subst a b => Bind p b -> [a] -> b
instantiate_ (B _p t) u = substBvs initialCtx u t


-- | Instances of @'Subst' b a@ are terms of type @a@ that may contain
-- variables of type @b@ that may participate in capture-avoiding
-- substitution.
class Subst b a where
  -- | This is the only method that must be implemented
  isvar :: a -> Maybe (SubstName a b)
  isvar _ = Nothing

  -- | This is an alternative version to 'isvar', useable in the case
  --   that the substituted argument doesn't have *exactly* the same type
  --   as the term it should be substituted into.
  --   The default implementation always returns 'Nothing'.
  isCoerceVar :: a -> Maybe (SubstCoerce a b)
  isCoerceVar _ = Nothing

  -- | @'subst' nm e tm@ substitutes @e@ for @nm@ in @tm@.  It has
  -- a default generic implementation in terms of @isvar@
  subst :: Name b -> b -> a -> a
  default subst :: (Generic a, GSubst b (Rep a)) => Name b -> b -> a -> a
  subst n u x =
    if (isFreeName n)
    then case (isvar x :: Maybe (SubstName a b)) of
      Just (SubstName m) | m == n -> u
      _ -> case (isCoerceVar x :: Maybe (SubstCoerce a b)) of
        Just (SubstCoerce m f) | m == n -> maybe x id (f u)
        _ -> to $ gsubst n u (from x)
    else error $ "Cannot substitute for bound variable " ++ show n

  substs :: [(Name b, b)] -> a -> a
  default substs :: (Generic a, GSubst b (Rep a)) => [(Name b, b)] -> a -> a
  substs ss x
    | all (isFreeName . fst) ss =
      case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) | Just (_, u) <- find ((==m) . fst) ss -> u
        _ -> case isCoerceVar x :: Maybe (SubstCoerce a b) of
            Just (SubstCoerce m f) | Just (_, u) <- find ((==m) . fst) ss -> maybe x id (f u)
            _ -> to $ gsubsts ss (from x)
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

   -- Bound variable substitution (replace a single pattern variable with a list of terms)
   -- Similar to open, but replaces with b's instead of with names
   -- Does not check whether enough b's are provided: will ignore extra if there are too many
   -- and skip the substitution if there are too few.
  substBvs :: AlphaCtx -> [b] -> a -> a
  default substBvs :: (Generic a, GSubst b (Rep a)) => AlphaCtx -> [b] -> a -> a
  substBvs ctx bs x =
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName (Bn j k)) | ctxLevel ctx == j, fromInteger k < length bs -> bs !! fromInteger k
        _ -> to $ gsubstBvs ctx bs (from x)

instance Subst b c => GSubst b (K1 i c) where
  gsubst nm val = K1 . subst nm val . unK1
  gsubsts ss = K1 . substs ss . unK1
  gsubstBvs ctx b = K1 . substBvs ctx b . unK1

-- these have a Generic instance, but
-- it's self-refential (ie: Rep Int = D1 (C1 (S1 (Rec0 Int))))
-- so our structural GSubst instances get stuck in an infinite loop.
instance Subst b Int where subst _ _ = id ; substs _ = id ; substBvs _ _ = id
instance Subst b Bool where subst _ _ = id ; substs _ = id ; substBvs _ _ = id
instance Subst b () where subst _ _ = id ; substs _ = id ; substBvs _ _ = id
instance Subst b Char where subst _ _ = id ; substs _ = id ; substBvs _ _ = id
instance Subst b Float where subst _ _ = id ; substs _ = id ; substBvs _ _ = id
instance Subst b Double where subst _ _ = id ; substs _ = id ; substBvs _ _ = id

-- huh, apparently there's no instance Generic Integer.
instance Subst b Integer where subst _ _ = id ; substs _ = id ; substBvs _ _ = id

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (NonEmpty a)
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)

instance Subst b (Name a) where subst _ _ = id  ; substs _ = id ; substBvs _ _ = id
instance Subst b AnyName where subst _ _ = id ; substs _ = id ; substBvs _ _ = id

instance (Subst c a) => Subst c (Embed a) where
  substBvs c us (Embed x)
    | isTermCtx c = Embed (substBvs (termCtx c) us x)
    | otherwise = error "Internal error: substBvs on Embed"

instance (Subst c e) => Subst c (Shift e) where
  subst x b (Shift e) = Shift (subst x b e)
  substs ss (Shift e) = Shift (substs ss e)
  substBvs c b (Shift e) = Shift (substBvs (decrLevelCtx c) b e)

instance (Subst c b, Subst c a, Alpha a, Alpha b) => Subst c (Bind a b) where
  substBvs c b (B p t) = B (substBvs (patternCtx c) b p) (substBvs (incrLevelCtx c) b t)

instance (Subst c p1, Subst c p2) => Subst c (Rebind p1 p2) where
  substBvs c us (Rebnd p q) = Rebnd (substBvs c us p) (substBvs (incrLevelCtx c) us q)

instance (Subst c p) => Subst c (Rec p) where
  substBvs c us (Rec p) = Rec (substBvs (incrLevelCtx c) us p)

instance (Alpha p, Subst c p) => Subst c (TRec p) where
  substBvs c us (TRec p) = TRec (substBvs (patternCtx (incrLevelCtx c)) us p)

instance Subst a (Ignore b) where
  subst _ _ = id
  substs _ = id
  substBvs _ _ = id

-- | Specialized version of capture-avoiding substitution for that operates on a @'Bind' ('Name' a) t@ term to @'unbind'@
-- the bound name @Name a@ and immediately subsitute a new term for its occurrences.
--
-- This is a specialization of @'instantiate' :: Bind pat term -> [a] -> term@ where the @'Bind' pat term@ has a pattern that is just
-- a single @'Name' a@ and there is a single substitution term of type @a@.  Unlike 'instantiate', this function cannot fail at runtime.
substBind :: Subst a t => Bind (Name a) t -> a -> t
substBind b u = instantiate_ b [u]

