module Unbound.Generics.LocallyNameless.Internal.Lens where

import Control.Monad.Reader (MonadReader(..))
import qualified Control.Monad.Reader as Reader
import Control.Applicative (Const(..))

type Getting r s a = (a -> Const r a) -> s -> Const r s

view :: MonadReader s m => Getting a s a -> m a
view l = Reader.asks (getConst . l Const)
{-# INLINE view #-}
