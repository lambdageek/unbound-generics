{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.LFresh
-- Copyright  : (c) 2011, Stephanie Weirich
-- License    : BSD3 (See LFresh.hs)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Local freshness monad.
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
{-# LANGUAGE GeneralizedNewtypeDeriving
             , FlexibleInstances
             , MultiParamTypeClasses
             , UndecidableInstances #-}
module Unbound.Generics.LocallyNameless.LFresh
       (
         -- * The 'LFresh' class

         LFresh(..),

         LFreshM, runLFreshM, contLFreshM,
         LFreshMT(..), runLFreshMT, contLFreshMT

       ) where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Monoid
import Data.Typeable (Typeable)

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Applicative (Applicative, Alternative)

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Error
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.Writer.Class as WC

import Unbound.Generics.LocallyNameless.Name

-- | This is the class of monads that support freshness in an
--   (implicit) local scope.  Generated names are fresh for the current
--   local scope, not necessarily globally fresh.
class Monad m => LFresh m where
  -- | Pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: Typeable a => Name a -> m (Name a)
  -- | Avoid the given names when freshening in the subcomputation,
  --   that is, add the given names to the in-scope set.
  avoid   :: [AnyName] -> m a -> m a
  -- | Get the set of names currently being avoided.
  getAvoids :: m (Set AnyName)

-- | The LFresh monad transformer.  Keeps track of a set of names to
-- avoid, and when asked for a fresh one will choose the first numeric
-- prefix of the given name which is currently unused.
newtype LFreshMT m a = LFreshMT { unLFreshMT :: ReaderT (Set AnyName) m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadIO, MonadPlus, MonadFix)

-- | Run an 'LFreshMT' computation in an empty context.
runLFreshMT :: LFreshMT m a -> m a
runLFreshMT m = contLFreshMT m S.empty

-- | Run an 'LFreshMT' computation given a set of names to avoid.
contLFreshMT :: LFreshMT m a -> Set AnyName -> m a
contLFreshMT (LFreshMT m) = runReaderT m

instance Monad m => LFresh (LFreshMT m) where
  lfresh nm = LFreshMT $ do
    let s = name2String nm
    used <- ask
    return $ head (filter (\x -> not (S.member (AnyName x) used))
                          (map (makeName s) [0..]))
  avoid names = LFreshMT . local (S.union (S.fromList names)) . unLFreshMT

  getAvoids = LFreshMT ask

-- | A convenient monad which is an instance of 'LFresh'.  It keeps
--   track of a set of names to avoid, and when asked for a fresh one
--   will choose the first unused numerical name.
type LFreshM = LFreshMT Identity

-- | Run a LFreshM computation in an empty context.
runLFreshM :: LFreshM a -> a
runLFreshM = runIdentity . runLFreshMT

-- | Run a LFreshM computation given a set of names to avoid.
contLFreshM :: LFreshM a -> Set AnyName -> a
contLFreshM m = runIdentity . contLFreshMT m

instance LFresh m => LFresh (ContT r m) where
  lfresh = lift . lfresh
  avoid  = mapContT . avoid
  getAvoids = lift getAvoids

instance (Error e, LFresh m) => LFresh (ErrorT e m) where
  lfresh = lift . lfresh
  avoid  = mapErrorT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (IdentityT m) where
  lfresh = lift . lfresh
  avoid  = mapIdentityT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (ListT m) where
  lfresh = lift . lfresh
  avoid  = mapListT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (MaybeT m) where
  lfresh = lift . lfresh
  avoid  = mapMaybeT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (ReaderT r m) where
  lfresh = lift . lfresh
  avoid  = mapReaderT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (Lazy.StateT s m) where
  lfresh = lift . lfresh
  avoid  = Lazy.mapStateT . avoid
  getAvoids = lift getAvoids

instance LFresh m => LFresh (Strict.StateT s m) where
  lfresh = lift . lfresh
  avoid  = Strict.mapStateT . avoid
  getAvoids = lift getAvoids

instance (Monoid w, LFresh m) => LFresh (Lazy.WriterT w m) where
  lfresh = lift . lfresh
  avoid  = Lazy.mapWriterT . avoid
  getAvoids = lift getAvoids

instance (Monoid w, LFresh m) => LFresh (Strict.WriterT w m) where
  lfresh = lift . lfresh
  avoid  = Strict.mapWriterT . avoid
  getAvoids = lift getAvoids

-- Instances for applying LFreshMT to other monads

instance MonadTrans LFreshMT where
  lift = LFreshMT . lift

instance CC.MonadCont m => CC.MonadCont (LFreshMT m) where
  callCC c = LFreshMT $ CC.callCC (unLFreshMT . (\k -> c (LFreshMT . k)))

instance EC.MonadError e m => EC.MonadError e (LFreshMT m) where
  throwError = lift . EC.throwError
  catchError m h = LFreshMT $ EC.catchError (unLFreshMT m) (unLFreshMT . h)

instance StC.MonadState s m => StC.MonadState s (LFreshMT m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (LFreshMT m) where
  ask   = lift RC.ask
  local f = LFreshMT . mapReaderT (RC.local f) . unLFreshMT

instance WC.MonadWriter w m => WC.MonadWriter w (LFreshMT m) where
  tell   = lift . WC.tell
  listen = LFreshMT . WC.listen . unLFreshMT
  pass   = LFreshMT . WC.pass . unLFreshMT
