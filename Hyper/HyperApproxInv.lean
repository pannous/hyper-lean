/-
  Approximate inverse for R*, via truncated geometric series.
  ================================================================

  `Field R*`'s `mul_inv_cancel` is a documented `sorry` (`Hyper/HyperList.lean`)
  because general multi-term `R*` values genuinely have no *exact* finite
  inverse — `1/(1+ε) = 1 - ε + ε² - ε³ + …` needs infinitely many terms,
  impossible in a finite-support list. This mirrors `Hyper/old/HyperGeneralField.lean`'s
  `AlmostField` idea for a different model (`HGReal = Lex (AddMonoidAlgebra ℝ ℤ)`,
  `noncomputable` throughout since its coefficients are `ℝ`) — same
  mathematical shape, ported to `R*`'s own `ℚ`-coefficient, `List`-based,
  `native_decide`-friendly representation instead.

  ⚠️ Why this works for `R*`'s `1/(ε+ω)` but NOT for `PiEField`'s `1/(π+e)`
  (see `Hyper/HyperFieldOfFractions.lean` for that case instead): the
  factoring step below relies on `x`'s non-leading terms being genuinely
  *infinitesimal relative to its own leading term* — dividing by the leading
  monomial always produces a remainder of strictly negative order, and
  strictly-negative-order values are the ones `R*`'s own order structure
  already treats as "smaller and smaller" as the order decreases, which is
  exactly what makes a truncated geometric series an *improving*
  approximation. `π` and `e` have no such structure — they're both flat,
  "order 0" formal generators, not infinitesimals — so `π/e` (needed to
  factor `π+e = e·(1+π/e)`) is just an ordinary-sized value, not a shrinking
  one, and the same truncation trick would not converge.

  ⚠️ Scope: the geometric identity below is checked concretely
  (`native_decide` on `ε+ω`, `1+ε`), not proved `∀ x n`. A general proof
  needs `CommRing`-level lemmas (`mul_comm`, distributivity) for `R*`'s
  *direct* `Add`/`Mul` instances specifically — Mathlib's own
  `mul_neg_geom_sum` and the `ring` tactic both resolve against the
  `Field R*` instance's *separately bundled* operations instead (the
  documented instance diamond, `Hyper/probes/EvalsAdvanced.lean`), and since
  that instance's `mul_inv_cancel` is `sorry`, anything routed through it
  becomes `noncomputable` — confirmed directly: `mul_neg_geom_sum`-based and
  `ring`-based attempts both failed to compile for exactly this reason. Not
  a proof gap glossed over; a concretely-hit wall, worth closing separately
  by proving `R*`'s direct-instance ring lemmas standalone (not attempted
  here, out of scope for "quick").
-/
import Hyper.HyperList

open Hypers

namespace Hypers.HyperLists

/-- `x ^ n` by repeated multiplication (same reasoning as
    `Hyper/HyperTranscendental.lean`'s `hpow`: avoids the `Field R*`
    instance's `^`, which is diamond/`sorry`-tainted). -/
def hpow (x : R*) : ℕ → R*
  | 0 => 1
  | (n + 1) => x * hpow x n

/-- `Σ_{k<n} (-d)^k`, hand-recursed (not `Finset.sum`, for the same reason
    as `hpow`). -/
def geomSum (d : R*) : ℕ → R*
  | 0 => 0
  | (n + 1) => geomSum d n + hpow (-d) n

/-- Approximate inverse of `x`, truncated at `n` terms. Factors out `x`'s
    own leading monomial first (`(lead x)⁻¹` is *exact* — `Inv` is exact for
    single terms) so the remainder `δ := (lead x)⁻¹ * x - 1` consists purely
    of negative-order (genuinely infinitesimal) terms, matching
    `Hyper/old/HyperGeneralField.lean`'s `HG_approxInv` construction. -/
def approxInv (x : R*) (n : ℕ) : R* := (lead x)⁻¹ * geomSum ((lead x)⁻¹ * x - 1) n

-- ═══════════════════════════════════════════════════════════════════════════
-- Concrete checks: the remainder is exactly `-(-δ)^n`, matching the
-- geometric-sum identity `(1+δ)·Σ(-δ)^k = 1-(-δ)^n` — verified on instances,
-- not (yet) as a general theorem; see the file header for why.
-- ═══════════════════════════════════════════════════════════════════════════

-- ε+ω: leading term ω, δ = ω⁻¹(ε+ω) - 1 = ε(ε+ω) - 1 = ε² (genuinely
-- infinitesimal, order -2). Remainder after 3 terms: -(-ε²)³ = ε⁶.
#eval approxInv (ε + ω : R*) 3 -- ε - ε³ + ε⁵
example : (ε + ω : R*) * approxInv (ε + ω) 3 = 1 + ε * ε * ε * ε * ε * ε := by native_decide

-- 1+ε (the AlmostField literature's own headline example): leading term 1,
-- δ = ε. Remainder after 4 terms: -(-ε)⁴ = -ε⁴.
#eval approxInv ((1 : R*) + ε) 4 -- 1 - ε + ε² - ε³
example : ((1 : R*) + ε) * approxInv ((1 : R*) + ε) 4 = 1 - ε * ε * ε * ε := by native_decide

-- More terms genuinely improve the approximation (it's not a fixed point).
example : approxInv ((1 : R*) + ε) 5 ≠ approxInv ((1 : R*) + ε) 4 := by native_decide

end Hypers.HyperLists
