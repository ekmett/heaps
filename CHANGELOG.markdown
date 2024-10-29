next [????.??.??]
-----------------
* Drop support for pre-8.0 versions of GHC.

0.4 [2021.02.17]
----------------
* `heaps` now always exports a `null` function that is specialized to `Heap`,
  i.e.,

  ```haskell
  null :: Heap a -> Bool
  ```

  Previously, this specialized versions of `null` was only exported with GHC
  7.8 or older, and for more recent GHCs, the `Data.Foldable` version was
  exported instead. The exported API is now uniform across all supported
  versions of GHC.
* Export `adjustMin`.

0.3.6.1 [2019.02.05]
--------------------
* Change to `build-type: Simple`, and drop the `doctests` test suite. This was
  done in an effort to make `heaps`' dependency footprint as minimal as
  possible, since `heaps` is used to bootstrap `shake`.
* Fix the Haddocks for `span`.

0.3.6 [2018.01.18]
------------------
* Add `Semigroup` instance for `Heap`.

0.3.5
-----
* Support `doctest-0.12`

0.3.4.1
-------
* Fix a typo in the `doctests` for `mapMonotonic`

0.3.4
-----
* Add `Bifunctor Entry` instance
* Revamp `Setup.hs` to use `cabal-doctest`. This makes it build
  with `Cabal-2.0`, and makes the `doctest`s work with `cabal new-build` and
  sandboxes.

0.3.3
-----
* Remove redundant constraints
* Build warning-free on GHC 8.0-rc1

0.3.2.1
-------
* Haddock fix

0.3.2
-----
* Build without warnings on GHC 7.10
* Overload Foldable `null` and `length` on GHC 7.10+

0.3.1
-----
* Explicit nominal role annotation

0.3.0.1
-------
* Nicer formatting of the haddocks

