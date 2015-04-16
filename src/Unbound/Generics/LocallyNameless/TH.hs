{-# OPTIONS_HADDOCK show-extensions #-}
-- |
-- Module     : Unbound.Generics.LocallyNameless.TH
-- Copyright  : (c) 2015, Aleksey Kliger
-- License    : BSD3 (See LICENSE)
-- Maintainer : Aleksey Kliger
-- Stability  : experimental
--
-- Template Haskell methods to construct instances of 'Alpha' for
-- datatypes that don't contain any names and don't participate in
-- 'Alpha' operations in any non-trivial way.
{-# LANGUAGE TemplateHaskell #-}
module Unbound.Generics.LocallyNameless.TH (makeClosedAlpha) where
import Language.Haskell.TH

import Control.Applicative (Applicative(..))
import Data.Monoid (Monoid(..))
import Unbound.Generics.LocallyNameless.Alpha (Alpha(..))

-- | Make a trivial @instance 'Alpha' T@ for a type @T@ that does not
-- contains no bound nor free values of type @'Name' a@ or @'AnyName'@
-- (or any in general any values that are themselves non-trivial
-- instances of 'Alpha').  Use this to write 'Alpha' instances for
-- types that you don't want to traverse via their @GHC.Generics.Rep@
-- representation just to find out that there aren't any names.
--
-- @@@
-- data T = T Int deriving (Eq, Ord, Show)
-- $(makeClosedAlpha T)
-- -- constructs
-- -- instance Alpha T where
-- --   aeq' _ = (==)
-- --   acompare' _ = compare
-- --   fvAny' _ _ = pure
-- --   close _ _ = id
-- --   open _ _ = id
-- --   isPat _ = mempty
-- --   isTerm _ = True
-- --   nthPatFind _ = Left
-- --   namePatFind _ _ = Left 0
-- --   swaps' _ _ = id
-- --   freshen' _ i = return (i, mempty)
-- --   lfreshen' _ i cont = cont i mempty
-- @@@
--
makeClosedAlpha :: Name -> DecsQ
makeClosedAlpha tyName = do
  
  let valueD vName e = valD (varP vName) (normalB e) []
      -- methods :: [Q Dec]
      methods =
             [
               valueD (mkName "aeq'")      [e| \_ctx        -> (==)               |]
             , valueD (mkName "fvAny'")    [e| \_ctx _nfn   -> pure               |]
             , valueD 'close               [e| \_ctx _b     -> id                 |]
             , valueD 'open                [e| \_ctx _b     -> id                 |]
             , valueD 'isPat               [e| \_           -> mempty             |]
             , valueD 'isTerm              [e| \_           -> True               |]
             , valueD 'nthPatFind          [e| \_           -> Left               |]
             , valueD 'namePatFind         [e| \_ _         -> Left 0             |]
             , valueD (mkName "swaps'")    [e| \_ctx _p     -> id                 |]
             , valueD (mkName "freshen'")  [e| \_ctx i      -> return (i, mempty) |]
             , valueD (mkName "lfreshen'") [e| \_ctx i cont -> cont i mempty      |]
             , valueD (mkName "acompare'") [e| \_ctx        -> compare            |]
             ]
  d <- instanceD (cxt []) (appT [t|Alpha|] (conT tyName)) methods
  return [d]

