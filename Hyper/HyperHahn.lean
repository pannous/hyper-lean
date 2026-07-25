import Mathlib

/-!
Exploration: swap `R*`'s finite-`List (ℚ×ℚ)` representation for Mathlib's
`HahnSeries ℚ ℚ` (well-ordered-support formal series) — see
`notes/hahn-series-tradeoff.md` for the full writeup. Findings:

**What it fixes for free**: `HahnSeries.instField` (in
`Mathlib.RingTheory.HahnSeries.Summable`) is a genuine `Field` instance,
requiring only `[AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
[Field R]` — satisfied by `Γ = R = ℚ` with no extra work. `mul_inv_cancel`
below is a real theorem, not the `sorry` it is in `Hyper/HyperList.lean`.
`ring` also works directly (no Add/Mul instance diamond, unlike `R*`).

**What it costs**: `Mathlib.RingTheory.HahnSeries.{Basic,Multiplication,
Summable}` are ALL wrapped in `noncomputable section` — confirmed empirically
below, `#eval`/`native_decide`/`decide` do not work on `HahnSeries` at all
(no `Decidable` instance for equality, since it isn't a finite check on
infinite well-ordered support in general). Every fact needs a `simp`/`rw`
proof by named lemma instead of "compute and check" — a fundamentally
different proof style from every other file in `Hyper/`, which is built
almost entirely on `native_decide` over concrete `R*` terms.

**Conclusion: NOT a drop-in swap.** This is the central finding: adopting
`HahnSeries` for the reference model would eliminate the eval-driven
probe methodology the whole project (and its `probes/` files) is built on,
in exchange for a real `Field` instance and exact transcendentals. Not
recommended as a wholesale replacement for `Hyper/HyperList.lean`; kept here
as a standalone experiment in case a future task specifically wants the
proof-only, genuinely-a-field route (e.g. exact `exp`/`log`, see
`notes/transcendentals.md`).
-/

noncomputable section

namespace Hyper.Hahn

def eps : HahnSeries ℚ ℚ := HahnSeries.single (-1) 1
def omega : HahnSeries ℚ ℚ := HahnSeries.single 1 1

example : eps * omega = 1 := by
  unfold eps omega
  rw [HahnSeries.single_mul_single]
  norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- The actual payoff: a genuine multiplicative inverse for a MULTI-TERM
-- element, `(1 + eps)⁻¹` — exactly what `Field R*`'s `mul_inv_cancel` in
-- `Hyper/HyperList.lean` cannot provide (it's `sorry`'d there because the
-- finite-list representation structurally can't hold the inverse, which
-- needs infinitely many terms: `(1+ε)⁻¹ = 1 - ε + ε² - ε³ + …`).
-- ═══════════════════════════════════════════════════════════════════════════

example : (1 + eps) * (1 + eps)⁻¹ = 1 := by
  have h : (1 + eps : HahnSeries ℚ ℚ) ≠ 0 := by
    intro hc
    have := congrArg (·.coeff 0) hc
    simp [eps] at this
  exact mul_inv_cancel₀ h

-- ring works directly — no instance diamond, unlike R* (see EvalsAdvanced.lean).
example (x y z : HahnSeries ℚ ℚ) : x * (y + z) = x * y + x * z := by ring
example (x y : HahnSeries ℚ ℚ) : x + y = y + x := by ring

end Hyper.Hahn

end
