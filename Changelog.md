# NEXT

# 0.3.3

* Bump `exceptions` upper bound to support `0.10.0`

# 0.3.2

* Bump `deepseq >= 1.4.0.0` remove benchmark dependency on `deepseq-generics`
* Tested with GHC 8.4.1
* Tested with GHC 8.2.2
* Compile with `-Wcompat`
* Add `Semigroup` instances for all types that were previously `Monoid` instances
* Added more examples to the [examples/ directory](https://github.com/lambdageek/unbound-generics/tree/master/examples)
* Added "exceptions" dependency and `MonadThrow`, `MonadCatch`, `MonadMask` instances for `FreshMT` and `LFreshMT`.
  Thanks Alex McKenna.

# 0.3.1

* Tested with GHC 8.0.1
* Removed `Generic b` constraint from `Subst b (Name a)` instance.


# 0.3

* Change types of `open` and `close` to take `NthPatFind` and `NamePatFind` instead of generic patterns, update call sites.
* Add newtype wrappers and Monoid instances for `NthPatFind` and `NamePatFind`
* Change `isTerm` to return `All` instead of `Bool`

# 0.2

* Incorporating some of the extras/oversights from
  [clash-lib Unbound.Generics.LocallyNameless.Extra](https://github.com/clash-lang/clash-compiler/blob/master/clash-lib/src/Unbound/Generics/LocallyNameless/Extra.hs)

	* Make `Embed` an instance of `Ord`
	* `NFData` instances (see below)

* Re-implement `freshen'` and `gfreshen` using a free monad to give
  GHC a chance to inline it all away.  This changes the type of
  `gfreshen`.  Major version bump.

	* Expose `FFM`, `liftFFM` and `retractFFM`

* Provide `NFData` instances for all the combinators.
  Depend on 'deepseq'

* Start benchmarking some of the operations (particularly `unbind`).

# 0.1.2.1

* Fix ghc-7.10 build.
* Haddock cleanup.

# 0.1.2

* Added `IsEmbed` typeclass

    * Depend on 'profunctors'

* Changed `embed` and `unembed` to work over any `IsEmbed` type.

* Added `Shift` type for shifting the scope of embedded terms out one level.

# 0.1.1

* Added `isNullDisjointSet` function.
* Implement a TH `makeClosedAlpha` splice for constructing trivial leaf instances.

# 0.1

* Add `acompare` functiona and `acompare'` method to `Alpha` typeclass.  (christiaanb)

    Handwritten `Alpha` instances will need to define this additional
    method now.  Major version bump.

# 0.0.3

* Add 'name2Integer' method (christiaanb)
* Export internal type-directed `gaeq`, `gopen`, `gclose`, etc
  functions from `Unbound.Generics.LocallyNameless.Alpha`.

    Allows definitions like:

        instance Alpha Term where
          aeq' _ (Prim t1 _dk1) (Prim t2 _dk2) = t1 == t2
          aeq' c t1             t2             = gaeq c (from t1) (from t2)


# 0.0.2.1

* Unconditionally add ErrorT and ExceptT instances using transformers-compat (bergmark)

# 0.0.2

* Add 'Rec' pattern and 'TRec' term combinators.

* Alpha instance for '()'

# 0.0.1

* Add 'lunbind2' function.

* Doc updates.

* Switch from 'HUnit' to 'Tasty' for testing.

# 0.0.0.90

* Initial (re-)implementation effort.
