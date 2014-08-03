-- |
-- Module     : Unbound.Generics.LocallyNameless.Subst
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- A typeclass for types that may participate in substitution
{-# LANGUAGE DefaultSignatures
             , FlexibleContexts
             , FlexibleInstances
             , GADTs
             , MultiParamTypeClasses
             , ScopedTypeVariables
             , TypeOperators
 #-}
module Unbound.Generics.LocallyNameless.Subst where

import GHC.Generics

import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Rebind

-- | See 'isVar'
data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

-- | See 'isCoerceVar'  
data SubstCoerce a b where  
  SubstCoerce :: Name b -> (b -> Maybe a) -> SubstCoerce a b

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
      Just (SubstName m) -> if m == n then u else x
      Nothing -> case (isCoerceVar x :: Maybe (SubstCoerce a b)) of
        Just (SubstCoerce m f) -> if m == n then maybe x id (f u) else x
        Nothing -> to $ gsubst n u (from x)
    else error $ "Cannot substitute for bound variable " ++ show n


---- generic structural substitution.

class GSubst b f where
  gsubst :: Name b -> b -> f c -> f c

instance Subst b c => GSubst b (K1 i c) where
  gsubst nm val = K1 . subst nm val . unK1

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst nm val = M1 . gsubst nm val . unM1

instance GSubst b U1 where
  gsubst _nm _val _ = U1

instance GSubst b V1 where
  gsubst _nm _val _ = undefined

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst nm val (f :*: g) = gsubst nm val f :*: gsubst nm val g

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst nm val (L1 f) = L1 $ gsubst nm val f
  gsubst nm val (R1 g) = R1 $ gsubst nm val g

-- these have a Generic instance, but
-- it's self-refential (ie: Rep Int = D1 (C1 (S1 (Rec0 Int))))
-- so our structural GSubst instances get stuck in an infinite loop.
instance Subst b Int where subst _ _ = id
instance Subst b Bool where subst _ _ = id
instance Subst b () where subst _ _ = id
instance Subst b Char where subst _ _ = id
instance Subst b Float where subst _ _ = id
instance Subst b Double where subst _ _ = id

-- huh, apparently there's no instance Generic Integer. 
instance Subst b Integer where subst _ _ i = i

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)

instance Generic a => Subst b (Name a) where subst _ _ = id
instance Subst b AnyName where subst _ _ = id

instance (Subst c a) => Subst c (Embed a)

instance (Subst c b, Subst c a, Alpha a, Alpha b) => Subst c (Bind a b)

instance (Subst c p1, Subst c p2) => Subst c (Rebind p1 p2)
