# unbound-generics

[![Build Status](https://travis-ci.org/lambdageek/unbound-generics.svg)](https://travis-ci.org/lambdageek/unbound-generics)


This is a reimplementation of (parts of) [unbound](http://hackage.haskell.org/package/unbound) but using [GHC generics](http://www.haskell.org/ghc/docs/latest/html/libraries/base-4.7.0.1/GHC-Generics.html) instead of [RepLib](https://hackage.haskell.org/package/RepLib).

## Differences from `unbound`

For the most part, I tried to keep the same methods with the same signatures.  However there are a few differences.

1. `fv :: Alpha t => Fold t (Name n)`

   The `fv` method returns a `Fold` (in the sense of the [lens](http://hackage.haskell.org/package/lens) library),
   rather than an `Unbound.Util.Collection` instance.  That means you will generally have to write `toListOf fv t` or some    other summary operation.

2. `isPat :: Alpha t => t -> DisjointSet AnyName`

   You should only notice this if you're implementing an instance of `Alpha` by hand (rather than by using the default
   generic instance).  The original `unbound` returned a `Maybe [AnyName]` here with the same interpretation as `DisjointSet`: `Nothing` means an inconsistency was encountered, or `Just` the free variables of the pattern.
