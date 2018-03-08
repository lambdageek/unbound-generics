----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Generics.PermM
-- Copyright   :  (c) 2011, Stephanie Weirich <sweirich@cis.upenn.edu>
-- License     :  BSD-like (see PermM.hs)
-- Maintainer  :  Aleksey Kliger
-- Portability :  portable
--
-- A slow, but hopefully correct implementation of permutations.
--
----------------------------------------------------------------------
{-
Copyright (c)2011, Stephanie Weirich

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Stephanie Weirich nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}
{-# LANGUAGE PatternGuards #-}
module Unbound.Generics.PermM (
    Perm(..), permValid, single, compose, apply, support, isid, join, empty, restrict, mkPerm
  ) where

import Prelude (Eq(..), Show(..), (.), ($), Monad(return), Ord(..), Maybe(..), otherwise, (&&), Bool(..), id, uncurry, Functor(..))
import Data.List
import Data.Map (Map)
import Data.Semigroup as Sem
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Arrow ((&&&))
import Control.Monad ((>=>))

-- | A /permutation/ is a bijective function from names to names
--   which is the identity on all but a finite set of names.  They
--   form the basis for nominal approaches to binding, but can
--   also be useful in general.
newtype Perm a = Perm (Map a a)

-- | @'permValid' p@ returns @True@ iff the perumation is /valid/: if
-- each value in the range of the permutation is also a key.
permValid :: Ord a => Perm a -> Bool
permValid (Perm p) = all (\(_,v) -> M.member v p) (M.assocs p)
  -- a Map sends every key uniquely to a value by construction.  So if
  -- every value is also a key, the sizes of the domain and range must
  -- be equal and hence the mapping is a bijection.

instance Ord a => Eq (Perm a) where
  (Perm p1) == (Perm p2) =
    all (\x -> M.findWithDefault x x p1 == M.findWithDefault x x p2) (M.keys p1) &&
    all (\x -> M.findWithDefault x x p1 == M.findWithDefault x x p2) (M.keys p2)

instance Show a => Show (Perm a) where
  show (Perm p) = show p

-- | Apply a permutation to an element of the domain.
apply :: Ord a => Perm a -> a -> a
apply (Perm p) x = M.findWithDefault x x p

-- | Create a permutation which swaps two elements.
single :: Ord a => a -> a -> Perm a
single x y = if x == y then Perm M.empty else
    Perm (M.insert x y (M.insert y x M.empty))

-- | The empty (identity) permutation.
empty :: Perm a
empty = Perm M.empty

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
compose :: Ord a => Perm a -> Perm a -> Perm a
compose (Perm b) (Perm a) =
  Perm (M.fromList ([ (x,M.findWithDefault y y b) | (x,y) <- M.toList a]
         ++ [ (x, M.findWithDefault x x b) | x <- M.keys b, M.notMember x a]))

-- | Permutations form a semigroup under 'compose'.
-- @since 0.3.2
instance Ord a => Sem.Semigroup (Perm a) where
  (<>) = compose

-- | Permutations form a monoid with identity 'empty'.
instance Ord a => Monoid (Perm a) where
  mempty  = empty
  mappend = (<>)

-- | Is this the identity permutation?
isid :: Ord a => Perm a -> Bool
isid (Perm p) =
     M.foldrWithKey (\ a b r -> r && a == b) True p

-- | /Join/ two permutations by taking the union of their relation
--   graphs. Fail if they are inconsistent, i.e. map the same element
--   to two different elements.
join :: Ord a => Perm a -> Perm a -> Maybe (Perm a)
join (Perm p1) (Perm p2) =
     let overlap = M.intersectionWith (==) p1 p2 in
     if M.fold (&&) True overlap then
       Just (Perm (M.union p1 p2))
       else Nothing

-- | The /support/ of a permutation is the set of elements which are
--   not fixed.
support :: Ord a => Perm a -> [a]
support (Perm p) = [ x | x <- M.keys p, M.findWithDefault x x p /= x]

-- | Restrict a permutation to a certain domain.
restrict :: Ord a => Perm a -> [a] -> Perm a
restrict (Perm p) l = Perm (foldl' (\p' k -> M.delete k p') p l)

-- | A partial permutation consists of two maps, one in each direction
--   (inputs -> outputs and outputs -> inputs).
data PartialPerm a = PP (M.Map a a) (M.Map a a)
  deriving Show

emptyPP :: PartialPerm a
emptyPP = PP M.empty M.empty

extendPP :: Ord a => a -> a -> PartialPerm a -> Maybe (PartialPerm a)
extendPP x y pp@(PP mfwd mrev)
  | Just y' <- M.lookup x mfwd = if y == y' then Just pp
                                            else Nothing
  | Just x' <- M.lookup y mrev = if x == x' then Just pp
                                            else Nothing
  | otherwise = Just $ PP (M.insert x y mfwd) (M.insert y x mrev)

-- | Convert a partial permutation into a full permutation by closing
--   off any remaining open chains into a cycles.
ppToPerm :: Ord a => PartialPerm a -> Perm a
ppToPerm (PP mfwd mrev) = Perm $ foldr (uncurry M.insert) mfwd
                                       (map (findEnd &&& id) chainStarts)
        -- beginnings of open chains are elements which map to
        -- something in the forward direction but have no ancestor.
  where chainStarts = S.toList (M.keysSet mfwd `S.difference` M.keysSet mrev)
        findEnd x = case M.lookup x mfwd of
                      Nothing -> x
                      Just x' -> findEnd x'

-- | @mkPerm l1 l2@ creates a permutation that sends @l1@ to @l2@.
--   Fail if there is no such permutation, either because the lists
--   have different lengths or because they are inconsistent (which
--   can only happen if @l1@ or @l2@ have repeated elements).
mkPerm :: Ord a => [a] -> [a] -> Maybe (Perm a)
mkPerm xs ys
  | length xs /= length ys = Nothing
  | otherwise =
    fmap ppToPerm . ($emptyPP) . foldr (>=>) return $ zipWith extendPP xs ys
