# NEXT

# 0.4.0

* New binding specification type `Ignore`.

  Any two `Ignore T` terms will always be alpha-equivalent to each other, will
  be considered to contain no variables, and will not have any substitution
  apply beneath `Ignore`.  Useful for attaching annotation terms to your AST.

  ```haskell
    import Text.Parsec.Pos (SourcePos)
    
	data Expr =
	   ...
	   | Lambda (Ignore SourcePos) (Bind (Name Expr) Expr)
  ```

  As expected, any two `Lambda` expressions will be considered alpha-equivalent
  even if they differ in source position.

  Note that the `Ignore` will block operations on `Name a` for all `a`, which can be a little unexpected:

  ```haskell
    data Ty =
	  TyVar (Name Ty)
      | TyArr Ty Ty
    
    instance Subst Ty Ty where
	  ...

	data Expr =
	  ...
	  | Var (Name Expr)
	  | Lambda (Ignore Ty) (Bind (Name Expr) Expr)
    
     instance Subst Ty Expr
  ```

  Applying a substitution of a type for a free type variable to a `Lambda` will
  not descend into the `Ignore Ty`.

  Thanks Reed Mullanix (TOTWBF) for the new operation.

* Fix an issue in substitution where traversal would not continue in
  an AST node for which `isvar` or `isCoerceVar` is defined to return
  non-`Nothing` but which had additional structure.

  For example, in a language with meta variables and explicit substitutions:
  ```haskell
     data Expr =
	   ...
         -- normal variables that stand for expressions
       | Var (Name Expr)
          -- a meta variable occurrence and an explicit substitution
		  -- of expressions to substitute in for the free variables
	   | MetaVar (Name Meta) [(Name Expr, Expr)]
     -- a meta variable stands for an expression with some free term vars
	 data Meta = MetaVar Expr

     -- substitution for a meta in an expression
	 instance Subst Expr Meta where
	   isCoerceVar (MetaVar u sub) = Just (SubstCoerce u (Just . applyExplicitSubst sub))
	 applyExplicitSubst :: [(Name Expr, Expr)] -> Meta -> Expr
	 applyExplicitSubst s (MetaVar e) = substs s e
  ```

  Given an expression `e1` defined as `MetaVar "u" [("x", 10)]`, we may want to
  substitute a `Meta ("x" + "x")` for `"u"`  to get `10 + 10` (that is,
  we replace `"u"` by the expression `"x" + "x"` and immediately apply
  the substitution `10` for `"x"`).

  Now suppose we have an expression `e2` defined as `MetaVar "v" [("y",
  e1)]` (that is, an occurrence of meta var "v" together with a
  substitution of `e1` from above for `"y"`).  If we again try to
  substitute `Meta ("x" + "x")` for `"u"` in `e2`, we would expect to
  get `MetaVar "v" [("y", 10 + 10)]` (that is, since "v" is not equal to
  "u", we leave the meta var alone, but substitute for any occurrences
  of "u" in the explicit substitution, so `e1` becomes `10 + 10` as
  before).

  The bug in previous versions of `unbound-generics` was that we would
  incorrectly leave `MetaVar "v" [("y", e1)]` unchanged as soon as we
  saw that `isCoerceVar (MetaVar "v" [("y", e1)])` returned
  `Just (SubstCoerce "u" ...)` where `"u" /= "v"`.

  Thanks Reed Mullanix (TOTWBF) for finding and fixing this issue.
  https://github.com/lambdageek/unbound-generics/issues/26

# 0.3.4

* Bump `containers` upper bound to support `0.6`.
  (GHC 8.6.1 support)
  Thanks Christiaan Baaij.

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
