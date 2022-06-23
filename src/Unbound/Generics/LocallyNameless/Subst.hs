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
  ) where

import GHC.Generics

import Data.List (find)

import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Shift
import Unbound.Generics.LocallyNameless.Ignore
import Unbound.Generics.LocallyNameless.Bind
import Unbound.Generics.LocallyNameless.Rebind
import Unbound.Generics.LocallyNameless.Rec

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

  -- | @substPat ctx v tm@ substitutes for the bound variable @v@ in @tm@ in context @ctx@. See @'substBind'@
  substPat :: AlphaCtx -> b -> a -> a
  default substPat :: (Generic a, GSubst b (Rep a)) => AlphaCtx -> b -> a -> a
  substPat ctx u x =
    case (isvar x :: Maybe (SubstName a b)) of
      Just (SubstName (Bn j 0)) | ctxLevel ctx == j -> u
      _ -> to $ gsubstPat ctx u (from x)

---- generic structural substitution.

class GSubst b f where
  gsubst :: Name b -> b -> f c -> f c
  gsubsts :: [(Name b, b)] -> f c -> f c
  gsubstPat :: AlphaCtx -> b -> f c -> f c

instance Subst b c => GSubst b (K1 i c) where
  gsubst nm val = K1 . subst nm val . unK1
  gsubsts ss = K1 . substs ss . unK1
  gsubstPat ctx val = K1 . substPat ctx val . unK1

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst nm val = M1 . gsubst nm val . unM1
  gsubsts ss = M1 . gsubsts ss . unM1
  gsubstPat ctx val = M1 . gsubstPat ctx val . unM1

instance GSubst b U1 where
  gsubst _nm _val _ = U1
  gsubsts _ss _ = U1
  gsubstPat _ctx _val _ = U1

instance GSubst b V1 where
  gsubst _nm _val = id
  gsubsts _ss = id
  gsubstPat _ctx _val = id

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst nm val (f :*: g) = gsubst nm val f :*: gsubst nm val g
  gsubsts ss (f :*: g) = gsubsts ss f :*: gsubsts ss g
  gsubstPat ctx val (f :*: g) = gsubstPat ctx val f :*: gsubstPat ctx val g

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst nm val (L1 f) = L1 $ gsubst nm val f
  gsubst nm val (R1 g) = R1 $ gsubst nm val g

  gsubsts ss (L1 f) = L1 $ gsubsts ss f
  gsubsts ss (R1 g) = R1 $ gsubsts ss g

  gsubstPat ctx val (L1 f) = L1 $ gsubstPat ctx val f
  gsubstPat ctx val (R1 g) = R1 $ gsubstPat ctx val g

-- these have a Generic instance, but
-- it's self-refential (ie: Rep Int = D1 (C1 (S1 (Rec0 Int))))
-- so our structural GSubst instances get stuck in an infinite loop.
instance Subst b Int where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b Bool where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b () where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b Char where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b Float where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b Double where subst _ _ = id ; substs _ = id ; substPat _ _ = id

-- huh, apparently there's no instance Generic Integer. 
instance Subst b Integer where subst _ _ = id ; substs _ = id ; substPat _ _ = id

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)

instance Subst b (Name a) where subst _ _ = id ; substs _ = id ; substPat _ _ = id
instance Subst b AnyName where subst _ _ = id ; substs _ = id ; substPat _ _ = id

instance (Subst c a) => Subst c (Embed a) where
  substPat ctx val (Embed t) = Embed (substPat (termCtx ctx) val t)

instance (Subst c e) => Subst c (Shift e) where
  subst x b (Shift e) = Shift (subst x b e)
  substs ss (Shift e) = Shift (substs ss e)
  substPat ctx val (Shift e) = Shift (substPat (decrLevelCtx ctx) val e)

instance (Subst c b, Subst c a, Alpha a, Alpha b) => Subst c (Bind a b) where
  substPat ctx val (B p t) = B (substPat (patternCtx ctx) val p) (substPat (incrLevelCtx ctx) val t)

instance (Subst c p1, Subst c p2) => Subst c (Rebind p1 p2) where
  substPat ctx val (Rebnd p1 p2) = Rebnd (substPat ctx val p1) (substPat (incrLevelCtx ctx) val p2)

instance (Subst c p) => Subst c (Rec p) where
  substPat ctx val (Rec p) = Rec (substPat (incrLevelCtx ctx) val p)

instance (Alpha p, Subst c p) => Subst c (TRec p)

instance Subst a (Ignore b) where
  subst _ _ = id
  substs _ = id
  substPat _ _ = id

-- | Specialized version of capture-avoiding substitution for that operates on a @'Bind' ('Name' a) t@ term to @'unbind'@
-- the bound name @Name a@ and immediately subsitute a new term for its occurrences.
substBind :: Subst a t => Bind (Name a) t -> a -> t
substBind (B _ t) u = substPat initialCtx u t
