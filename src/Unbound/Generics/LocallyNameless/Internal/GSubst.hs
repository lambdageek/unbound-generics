-- |
-- Module     : Unbound.Generics.LocallyNameless.Subst
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- A typeclass for generic structural substitution.

{-# LANGUAGE
               FlexibleInstances
             , MultiParamTypeClasses
             , TypeOperators
 #-}

module Unbound.Generics.LocallyNameless.Internal.GSubst (
  GSubst(..)
  ) where

import GHC.Generics

import Unbound.Generics.LocallyNameless.Name
import Unbound.Generics.LocallyNameless.Alpha

---- generic structural substitution.

class GSubst b f where
  gsubst :: Name b -> b -> f c -> f c
  gsubsts :: [(Name b, b)] -> f c -> f c
  gsubstBvs :: AlphaCtx -> [b] -> f c -> f c

instance GSubst b f => GSubst b (M1 i c f) where
  gsubst nm val = M1 . gsubst nm val . unM1
  gsubsts ss = M1 . gsubsts ss . unM1
  gsubstBvs c b = M1 . gsubstBvs c b . unM1

instance GSubst b U1 where
  gsubst _nm _val _ = U1
  gsubsts _ss _ = U1
  gsubstBvs _c _b _ = U1

instance GSubst b V1 where
  gsubst _nm _val = id
  gsubsts _ss = id
  gsubstBvs _c _b = id

instance (GSubst b f, GSubst b g) => GSubst b (f :*: g) where
  gsubst nm val (f :*: g) = gsubst nm val f :*: gsubst nm val g
  gsubsts ss (f :*: g) = gsubsts ss f :*: gsubsts ss g
  gsubstBvs c b (f :*: g) = gsubstBvs c b f :*: gsubstBvs c b g

instance (GSubst b f, GSubst b g) => GSubst b (f :+: g) where
  gsubst nm val (L1 f) = L1 $ gsubst nm val f
  gsubst nm val (R1 g) = R1 $ gsubst nm val g

  gsubsts ss (L1 f) = L1 $ gsubsts ss f
  gsubsts ss (R1 g) = R1 $ gsubsts ss g

  gsubstBvs c b (L1 f) = L1 $ gsubstBvs c b f
  gsubstBvs c b (R1 g) = R1 $ gsubstBvs c b g
