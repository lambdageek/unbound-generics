# unbound-generics

[![Join the chat at https://gitter.im/lambdageek/unbound-generics](https://badges.gitter.im/Join%20Chat.svg)](https://gitter.im/lambdageek/unbound-generics?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

[![Hackage](https://img.shields.io/hackage/v/unbound-generics.svg)](https://hackage.haskell.org/package/unbound-generics)
[![Build Status](https://travis-ci.org/lambdageek/unbound-generics.svg)](https://travis-ci.org/lambdageek/unbound-generics)

Support for programming with names and binders using GHC Generics.

## Summary

Specify the binding structure of your data type with an expressive set of type combinators, and `unbound-generics`
handles the rest!  Automatically derives alpha-equivalence, free variable calculation, capture-avoiding substitution, and more. See [`Unbound.Generics.LocallyNameless`](src/Unbound/Generics/LocallyNameless.hs) to get started.

This is a reimplementation of (parts of) [unbound](http://hackage.haskell.org/package/unbound) but using [GHC generics](http://www.haskell.org/ghc/docs/latest/html/libraries/base-4.7.0.1/GHC-Generics.html) instead of [RepLib](https://hackage.haskell.org/package/RepLib).

## Examples

Some examples are in the `examples/` directory in the source.  And also at [unbound-generics on GitHub Pages](https://lambdageek.github.io/unbound-generics)

### Example: Untyped lambda calculus interpreter
Here is how you would implement call by value evaluation for the untyped lambda calculus:

```haskell
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric, MultiParamTypeClasses #-}
module UntypedLambdaCalc where
import Unbound.Generics.LocallyNameless
import GHC.Generics (Generic)
import Data.Typeable (Typeable)

-- | Variables stand for expressions
type Var = Name Expr

-- | Expressions
data Expr = V Var                -- ^ variables
          | Lam (Bind Var Expr) -- ^ lambdas bind a variable within a body expression
          | App Expr Expr       -- ^ application
          deriving (Show, Generic, Typeable)

-- Automatically construct alpha equivalence, free variable computation and binding operations.
instance Alpha Expr

-- semi-automatically implement capture avoiding substitution of expressions for expressions
instance Subst Expr Expr where
  -- `isvar` identifies the variable case in your AST.
  isvar (V x) = Just (SubstName x)
  isvar _     = Nothing

-- evaluation takes an expression and returns a value while using a source of fresh names
eval :: Expr -> FreshM Expr
eval (V x) = fail $ "unbound variable " ++ show x
eval e@(Lam {}) = return e
eval (App e1 e2) = do
  v1 <- eval e1
  v2 <- eval e2
  case v1 of
   (Lam bnd) -> do
     -- open the lambda by picking a fresh name for the bound variable x in body
     (x, body) <- unbind bnd
     let body' = subst x v2 body
     eval body'
   _ -> fail "application of non-lambda"

example :: Expr
example =
  let x = s2n "x"
      y = s2n "y"
      e = Lam $ bind x (Lam $ bind y (App (V y) (V x)))
  in runFreshM $ eval (App (App e e) e)
  
-- >>> example
-- Lam (<y> App (V 0@0) (Lam (<x> Lam (<y> App (V 0@0) (V 1@0)))))

```
## Differences from `unbound`

For the most part, I tried to keep the same methods with the same signatures.  However there are a few differences.

1. `fv :: Alpha t => Fold t (Name n)`

   The `fv` method returns a `Fold` (in the sense of the [lens](http://hackage.haskell.org/package/lens) library),
   rather than an `Unbound.Util.Collection` instance.  That means you will generally have to write `toListOf fv t` or some    other summary operation.

2. Utility methods in the `Alpha` class have different types.

   You should only notice this if you're implementing an instance of `Alpha` by hand (rather than by using the default
   generic instance).
   
   1. `isPat :: Alpha t => t -> DisjointSet AnyName`
     The original `unbound` returned a `Maybe [AnyName]` here with the same interpretation as `DisjointSet`: `Nothing` means an inconsistency was encountered, or `Just` the free variables of the pattern.
   2. `isTerm :: Alpha t => t -> All`
   3. `open :: Alpha t => AlphaCtx -> NthPatFind -> t -> t`, `close :: Alpha t => AlphaCtx -> NamePatFind -> t -> t` where `NthPatFind` and `NamePatFind` are newtypes

3. `embed :: IsEmbed e => Embedded e -> e` and `unembed :: IsEmbed e => e -> Embedded e`

    The typeclass `IsEmbed` has an `Iso` (again in the sense of the `lens` library) as a method instead of the above pair of methods.

    Again, you should only notice this if you're implementing your own types that are instances of `IsEmbed`.  The easiest thing to do is to use implement `embedded = iso yourEmbed yourUnembed` where `iso` comes from `lens`.  (Although you can also implement it in terms of `dimap` if you don't want to depend on lens)
