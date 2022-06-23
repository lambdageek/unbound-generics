-- |
-- Module     : Unbound.Generics.LocallyNameless.Fresh
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Global freshness monad.
{-# LANGUAGE CPP, GeneralizedNewtypeDeriving,
             FlexibleInstances, MultiParamTypeClasses,
             StandaloneDeriving,
             UndecidableInstances
  #-}
-- (we expect deprecation warnings about Control.Monad.Trans.Error)
{-# OPTIONS_GHC -Wwarn #-}
module Unbound.Generics.LocallyNameless.Fresh where

import Control.Applicative (Applicative, Alternative)
import Control.Monad ()

import Control.Monad.Identity

import Control.Monad.Catch (MonadThrow, MonadCatch, MonadMask)
#if MIN_VERSION_base(4,9,0)
import qualified Control.Monad.Fail as Fail
#endif
#if MIN_VERSION_mtl(2,3,0)
import Control.Monad (MonadPlus)
import Control.Monad.Fix (MonadFix)
#endif
import Control.Monad.Trans
import Control.Monad.Trans.Except
import Control.Monad.Trans.Error
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.Writer.Class as WC

import Data.Monoid (Monoid)

import qualified Control.Monad.State as St

import Unbound.Generics.LocallyNameless.Name

-- | The @Fresh@ type class governs monads which can generate new
--   globally unique 'Name's based on a given 'Name'.
class Monad m => Fresh m where

  -- | Generate a new globally unique name based on the given one.
  fresh :: Name a -> m (Name a)


-- | The @FreshM@ monad transformer.  Keeps track of the lowest index
--   still globally unused, and increments the index every time it is
--   asked for a fresh name.
newtype FreshMT m a = FreshMT { unFreshMT :: St.StateT Integer m a }
  deriving
    ( Functor
    , Applicative
    , Alternative
    , Monad
    , MonadIO
    , MonadPlus
    , MonadFix
    , MonadThrow
    , MonadCatch
    , MonadMask
    )

#if MIN_VERSION_base(4,9,0)
deriving instance Fail.MonadFail m => Fail.MonadFail (FreshMT m)
#endif

-- | Run a 'FreshMT' computation (with the global index starting at zero).
runFreshMT :: Monad m => FreshMT m a -> m a
runFreshMT m = contFreshMT m 0

-- | Run a 'FreshMT' computation given a starting index for fresh name
--   generation.
contFreshMT :: Monad m => FreshMT m a -> Integer -> m a
contFreshMT (FreshMT m) = St.evalStateT m

instance MonadTrans FreshMT where
  lift = FreshMT . lift

instance CC.MonadCont m => CC.MonadCont (FreshMT m) where
  callCC c = FreshMT $ CC.callCC (unFreshMT . (\k -> c (FreshMT . k)))

instance EC.MonadError e m => EC.MonadError e (FreshMT m) where
  throwError = lift . EC.throwError
  catchError m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

instance StC.MonadState s m => StC.MonadState s (FreshMT m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (FreshMT m) where
  ask   = lift RC.ask
  local f = FreshMT . RC.local f . unFreshMT

instance WC.MonadWriter w m => WC.MonadWriter w (FreshMT m) where
  tell   = lift . WC.tell
  listen = FreshMT . WC.listen . unFreshMT
  pass   = FreshMT . WC.pass . unFreshMT


instance Monad m => Fresh (FreshMT m) where
  fresh (Fn s _) = FreshMT $ do
    n <- St.get
    St.put $! n + 1
    return $ (Fn s n)
  fresh nm@(Bn {}) = return nm

instance (Error e, Fresh m) => Fresh (ErrorT e m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh

instance Fresh m => Fresh (MaybeT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ReaderT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Lazy.StateT s m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Strict.StateT s m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Lazy.WriterT w m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Strict.WriterT w m) where
  fresh = lift . fresh

------------------------------------------------------------
-- FreshM monad

-- | A convenient monad which is an instance of 'Fresh'.  It keeps
--   track of a global index used for generating fresh names, which is
--   incremented every time 'fresh' is called.
type FreshM = FreshMT Identity

-- | Run a FreshM computation (with the global index starting at zero).
runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshMT

-- | Run a FreshM computation given a starting index.
contFreshM :: FreshM a -> Integer -> a
contFreshM m = runIdentity . contFreshMT m
