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
