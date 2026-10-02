# TODO
- `lake build Hyper` fails (pre-existing, unrelated to transfer work, 2026-10-02): `Hyper/probes/EvalsAdvanced.lean:57` (`pointMass` no longer resolves as a function), `Hyper/bad/debug.lean` (import `Mathlib.Data.Real.Ereal` gone), `Hyper/bad/HyperDerivative.lean` (`HyperFun` unknown), `Hyper/bad/SingletonProbZero.lean` (binder errors). `bad/` might be excluded from the lean_lib globs instead.
- Germ transfer for rational exponents (ε^{1/2}, raw `HyperList`): read `(a,e)` as `a·s^e` with rpow; needs an ordered field on the fraction field of `AddMonoidAlgebra ℚ ℚ` first.
