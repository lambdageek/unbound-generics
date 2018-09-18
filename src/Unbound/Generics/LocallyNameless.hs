-- |
-- Module     : Unbound.Generics.LocallyNameless
-- Copyright  : (c) 2014, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
--
-- The purpose of @unbound-genrics@ is to simplify the construction of
-- data structures with rich variable binding structure by providing
-- generic implementations of alpha-equivalence ('aeq'), free variable
-- permutation ('swaps'), local and global variable freshness
-- ('lfresh', 'fresh'), 
--
--
-- 
-- See 'Alpha', 'Bind', "Unbound.Generics.LocallyNameless.Operations" for more information.
module Unbound.Generics.LocallyNameless (
  module Unbound.Generics.LocallyNameless.Alpha,
  module Unbound.Generics.LocallyNameless.Name,
  module Unbound.Generics.LocallyNameless.Operations,
  module Unbound.Generics.LocallyNameless.Bind,
  module Unbound.Generics.LocallyNameless.Ignore,
  module Unbound.Generics.LocallyNameless.Embed,
  module Unbound.Generics.LocallyNameless.Shift,
  module Unbound.Generics.LocallyNameless.Rebind,
  module Unbound.Generics.LocallyNameless.Rec,
  module Unbound.Generics.LocallyNameless.Fresh,
  module Unbound.Generics.LocallyNameless.LFresh,
  module Unbound.Generics.LocallyNameless.Subst
  ) where

import Unbound.Generics.LocallyNameless.Alpha
import Unbound.Generics.LocallyNameless.Name hiding (Bn, Fn)
import Unbound.Generics.LocallyNameless.Bind hiding (B)
import Unbound.Generics.LocallyNameless.Ignore hiding (I)
import Unbound.Generics.LocallyNameless.Embed
import Unbound.Generics.LocallyNameless.Shift
import Unbound.Generics.LocallyNameless.Rebind hiding (Rebnd)
import Unbound.Generics.LocallyNameless.Rec
import Unbound.Generics.LocallyNameless.Fresh
import Unbound.Generics.LocallyNameless.LFresh
import Unbound.Generics.LocallyNameless.Operations
import Unbound.Generics.LocallyNameless.Subst
