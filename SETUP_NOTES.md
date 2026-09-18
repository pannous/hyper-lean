# Reproducible Lean setup

This checkout pins Lean **4.27.0** in `lean-toolchain` and mathlib
**v4.27.0** (`a3a10db0e9d66acbebf76c5e6a135066525ac900`) in the Lake files.
The previous lockfile referenced an unavailable mathlib object and `stable`
could move independently of the toolchain.

Use checkout-local `.lake/packages`. Do not point it at the shared
`~/.lake/packages`: Lake may replace packages there when resolving a URL or
revision mismatch. On this checkout the old symlink was retained as
`.lake/packages-shared`; `.lake/packages` is now an ordinary local directory.

The first baseline attempt let Lake replace shared mathlib before this
isolation was in place. Its exact prior Git revision was not recoverable.
The shared mathlib source and compiled cache were repaired at **v4.28.0-rc1**,
matching the installed shared aesop/ProofWidgets/Qq release metadata, with
its own nested dependencies; the sibling shared dependency directories were
left intact. This project uses its separate pinned v4.27.0 dependencies.

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
