Changelog for the `singletons-base` project
===========================================

next [????.??.??]
-----------------
* Add `Data.Functor.{Compose,Product,Sum}.Singletons`.
* The types of various entities in `Data.Functor.Const.Singletons` and
  `Data.Proxy.Singletons` have been tweaked slightly such that their
  specificities match their term-level counterparts:

  ```diff
  -SConst :: forall {k} {a} {b :: k} (x :: a). Sing x -> Sing ('Const @a @b x)
  +SConst :: forall {k}  a  (b :: k) (x :: a). Sing x -> Sing ('Const @a @b x)

  -type ConstSym0 :: forall  k  a (b :: k). a ~> Const a b
  +type ConstSym0 :: forall {k} a (b :: k). a ~> Const a b

  -type ConstSym1 :: forall  k a  (b :: k). a -> Const a b
  +type ConstSym1 :: forall {k} a (b :: k). a -> Const a b

  -type ProxySym0 :: forall  k  (t :: k). Proxy t
  +type ProxySym0 :: forall {k} (t :: k). Proxy t
  ```

3.0 [2021.03.12]
----------------
* The `singletons` library has been split into three libraries:

  * The new `singletons` library is now a minimal library that only provides
    `Data.Singletons`, `Data.Singletons.Decide`, `Data.Singletons.Sigma`, and
    `Data.Singletons.ShowSing` (if compiled with GHC 8.6 or later).
    `singletons` now supports building GHCs back to GHC 8.0, as well as GHCJS.
  * The `singletons-th` library defines Template Haskell functionality for
    promoting and singling term-level definitions, but but nothing else. This
    library continues to require the latest stable release of GHC.
  * The `singletons-base` library defines promoted and singled versions of
    definitions from the `base` library, including the `Prelude`. This library
    continues to require the latest stable release of GHC.

  Consult the changelogs for `singletons` and `singletons-th` for changes
  specific to those libraries. For more information on this split, see the
  [relevant GitHub discussion](https://github.com/goldfirere/singletons/issues/420).
* Require building with GHC 9.0.
* The modules in `singletons-base` have been renamed to better reflect the
  modules from `base` from which they take inspiration. In particular, the
  following module renamings have been applied:

  * `Data.Singletons.CustomStar`            -> `Data.Singletons.Base.CustomStar`
  * `Data.Singletons.Prelude`               -> `Prelude.Singletons`
  * `Data.Singletons.Prelude.Applicative`   -> `Control.Applicative.Singletons`
  * `Data.Singletons.Prelude.Bool`          -> `Data.Bool.Singletons`
  * `Data.Singletons.Prelude.Const`         -> `Data.Functor.Const.Singletons`
  * `Data.Singletons.Prelude.Either`        -> `Data.Either.Singletons`
  * `Data.Singletons.Prelude.Enum`          -> `Data.Singletons.Base.Enum`
  * `Data.Singletons.Prelude.Eq`            -> `Data.Eq.Singletons`
  * `Data.Singletons.Prelude.Foldable`      -> `Data.Foldable.Singletons`
  * `Data.Singletons.Prelude.Function`      -> `Data.Function.Singletons`
  * `Data.Singletons.Prelude.Functor`       -> `Data.Functor.Const.Singletons`
  * `Data.Singletons.Prelude.Identity`      -> `Data.Functor.Identity.Singletons`
  * `Data.Singletons.Prelude.IsString`      -> `Data.String.Singletons`
  * `Data.Singletons.Prelude.Ord`           -> `Data.Ord.Singletons`
  * `Data.Singletons.Prelude.List`          -> `Data.List.Singletons`
  * `Data.Singletons.Prelude.List.NonEmpty` -> `Data.List.NonEmpty.Singletons`
  * `Data.Singletons.Prelude.Maybe`         -> `Data.Maybe.Singletons`
  * `Data.Singletons.Prelude.Monad`         -> `Control.Monad.Singletons`
  * `Data.Singletons.Prelude.Monad.Fail`    -> `Control.Monad.Fail.Singletons`
  * `Data.Singletons.Prelude.Monad.Zip`     -> `Control.Monad.Zip.Singletons`
  * `Data.Singletons.Prelude.Monoid`        -> `Data.Monoid.Singletons`
  * `Data.Singletons.Prelude.Proxy`         -> `Data.Proxy.Singletons`
  * `Data.Singletons.Prelude.Semigroup`     -> `Data.Semigroup.Singletons`
  * `Data.Singletons.Prelude.Show`          -> `Data.Show.Singletons`
  * `Data.Singletons.Prelude.Traversable`   -> `Data.Traversable.Singletons`
  * `Data.Singletons.Prelude.Tuple`         -> `Data.Tuple.Singletons`
  * `Data.Singletons.Prelude.Void`          -> `Data.Void.Singletons`
  * `Data.Singletons.TH`                    -> `Data.Singletons.Base.TH`
  * `Data.Singletons.TypeError`             -> `Data.Singletons.Base.TypeError`
  * `Data.Singletons.TypeLits`              -> `GHC.TypeLits.Singletons`
  * `Data.Singletons.TypeRepTYPE`           -> `Data.Singletons.Base.TypeRepTYPE`

  Note that modules that do not correspond to any particular module in `base`
  now have the prefix `Data.Singletons.Base.*`. This includes
  `Data.Singletons.Base.Enum`, a special module that exists to provide a
  home for the `Succ` and `Pred` promoted type families that is separate from
  `Prelude.Singletons` (which exports everything from `PEnum` _except_ `Succ`
  and `Pred`). This is done in an effort to make importing `Prelude.Singletons`
  less likely to induce name clashes with code that works over unary natural
  numbers, which often use the names "`Succ`" and "`Pred`".
* An effort has been made to make the API of `Prelude.Singletons` more closely
  mirror that of the `Prelude` in `base`. As a result, `Prelude.Singletons` now
  exports some different functions than it used to. In particular, it now
  exports the following:

  * `Until`/`sUntil`/`UntilSym{N}`
  * `type (++@#@$$$)`
  * `type (.@#@$$$$)`
  * `FlipSym3`
  * `type (!!)`/`(%!!)`/`type (!!@#@{$})`
  * `Length`/`sLength`/`LengthSym{N}`
  * `DropWhile`/`sDropWhile`
  * `LookupSym{N}`
  * `Unzip3Sym{N}`

  `Prelude.Singletons` also used to export some things that were _not_ exported
  by the `Prelude`. Accordingly, these exports have been removed from
  `Prelude.Singletons`. They are:

  * `(^)`/`(%^)`/`type (^@#@{$})`. Although the `Prelude` does define a
    function named `(^)`, it is more general than the one defined in
    `singletons-base`, which only works on `Nat`s. Import
    `GHC.TypeLits.Singletons` if you wish to use the `Nat`-specific versions.
  * `DefaultEq`, which has no counterpart in the `Prelude`.
    Import `Data.Eq.Singletons` if you wish to use this.
  * `bool_`, which has no counterpart in the `Prelude`.
    Import `Data.Bool.Singletons` if you wish to use this.
* Two previously public-facing modules—`Data.Singletons.Prelude.Base` and
  `Data.Singletons.Prelude.Num`—have been turned into internal modules. The
  contents of these modules are re-exported from `Prelude.Singletons`, so that
  can be used instead.
* Due to the `singletons` package split, the `Eq`, `Ord`, etc. instances for
  `SomeSing` are no longer provided in the `Data.Singletons` module in the
  `singletons` library. Instead, they are now provided in a new
  `Data.Singletons.Base.SomeSing` module, which defines `Eq`, `Ord`, etc.
  instances for `SomeSing` as orphans.
* The `PEq` class no longer uses `DefaultEq` as its default implementation for
  `(==)`. `DefaultEq`, despite its name, is actually not a suitable
  implementation for `(==)` for a good majority of singleton types
  (see the discussion in
  [this GitHub issue](https://github.com/goldfirere/singletons/issues/457)
  for more information). `(==)`'s default is now defined in terms of `(/=)`,
  just like its term-level counterpart in the `Eq` class.
* Since `base-4.15.0.0` now deprecates `Data.Singletons.Option` (in
  anticipation of its removal in a future version of `base`), this library no
  longer offers a singleton type for `Option`. Accordingly, the `option_`
  function has also been removed.
