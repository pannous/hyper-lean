# Reproducible Lean setup

This checkout pins Lean **4.34.1** in `lean-toolchain` and mathlib **v4.34.1**
in `lakefile.toml`, the same version as every other project under
`~/dev/script/lean4`.

Dependencies live in the one shared package directory: `lakefile.toml` sets
`packagesDir = "../.lake/packages"`, and `lean4/.lake/packages` is a symlink to
`~/.lake/packages`. Sharing is safe only while all projects pin the same
mathlib tag; bump them together (see `lean4/notes/shared-lake.md`).

For a fresh checkout:

```sh
lake exe cache get
./test.sh
```

`test.sh` first builds the modules used by the tests, then runs the legacy
regression file, the cell-integral examples, and `test_algebraic.lean`. Merely
running `lake env lean test_all.lean` can load a stale local `.olean` and miss
an error in its source dependency. This was observed in `HyperReal.lean`:
a missing `RatFun.Hyper` alias was repaired to `GHyper RatFun.ExactField`.

The new exact theory is in `Hyper/OrderedRational.lean`,
`Hyper/ContextIntegral.lean`, `Hyper/AlgebraicSupport.lean`, and
`Hyper/AlgebraicDart.lean`. Their proof audits permit no unfinished-proof or
legacy list-equality axioms. Historical experimental files and the old list
field still contain unresolved obligations; they are not part of this
trusted algebraic path. The targeted suite does not claim that every
historical file under `Hyper/old`, `Hyper/bad`, or `Hyper/theory` builds.

`Hyper/GeometricContent.lean` adds the Euclidean length derivation and
boundary-aware geometric square model. It is included in the same suite;
see [geometric content](notes/geometric-algebraic-content.md) for its exact
scope and the general polyhedral extension theorem still outside Lean.

See [the current foundations](notes/algebraic-hyperreal-foundations.md) for
the mathematical contract and the distinction between points, dots, and halos.
