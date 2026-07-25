# HahnSeries swap: what it actually costs

Explored in `Hyper/HyperHahn.lean`. Question: would swapping `R*` from
`List (ℚ×ℚ)` to Mathlib's `HahnSeries ℚ ℚ` fix `mul_inv_cancel` and give
exact `exp`/`log`, and can it be dropped into the main model?

## What it fixes
`HahnSeries.instField` (`Mathlib.RingTheory.HahnSeries.Summable`) is a real
`Field` instance for `Γ = R = ℚ` — `(1+ε)⁻¹` genuinely exists and
`mul_inv_cancel` is a proved theorem, not `sorry`. `ring` also works
directly, with no instance diamond (unlike `R*`, see `EvalsAdvanced.lean`).

## What it costs — the dealbreaker
`Mathlib.RingTheory.HahnSeries.{Basic,Multiplication,Summable}` are entirely
`noncomputable section`. Confirmed empirically:
- `#eval` on a `HahnSeries ℚ ℚ` value: no `Repr`/`ToString` instance.
- `example : eps * omega = 1 := by native_decide`: fails —
  `failed to synthesize Decidable (eps * omega = 1)`. Equality of two
  well-ordered-support series isn't a finite check in general, so there's no
  `DecidableEq` at all, not just a missing `native_decide` compilation path.

So every fact becomes a `simp`/`rw` proof by named lemma
(`HahnSeries.single_mul_single`, `mul_inv_cancel₀`, …) instead of
"compute and check". That's a different proof style from literally every
other file in `Hyper/` (`HyperList.lean`, all of `probes/`), which is built
on `native_decide` over concrete terms.

## Verdict
Not a drop-in swap for the reference model — it would kill the eval-driven
methodology the whole project runs on, in exchange for field-completeness
and (per `notes/transcendentals.md`) a path to exact `exp`/`log`. Worth
revisiting only if/when a task specifically needs the proof-only, genuinely-
a-field route. `Hyper/HyperHahn.lean` stays as a standalone, buildable
experiment — not imported anywhere, not wired into `HyperReal.lean`.
