import Hyper.HyperList

/-!
Evals for the algebraic derivative from the Readme (`∂f(x) := (f(x+ε) - f(x)) / ε`)
and the Heaviside step / Dirac delta it produces, made concrete on `R*`.

This is genuinely new ground for the project: everywhere else in `Hyper/`,
`ε`/`ω` are elements of `R*` being combined by `+`/`*`; here they're used to
probe *functions* `R* → R*`, which is what the Readme's derivative and
algebraic-δ sections are actually about (`∂f(x)=(f(x+ε)-f(x))/ε`, `H(x):=x≥0`,
`δ:=ω₀/2`).

⚠️ Division by `ε` specifically is fine here even though `Inv` is broken for
general multi-term `R*` elements (see `Field R*`'s `mul_inv_cancel := sorry`
in `Hyper/HyperList.lean`) — `ε` is a single monomial, and `Inv`'s termwise
`(r, e) ↦ (r⁻¹, -e)` is exactly correct for those. So `deriv`/`cderiv` below
multiply by `ω` directly (`ε⁻¹ = ω` on the nose, `native_decide`-checkable)
rather than going through the general `⁻¹`.

⚠️ `native_decide` needs a closed (variable-free) goal, so unlike the
algebraic identities elsewhere in `probes/`, the polynomial-derivative facts
below are only checked at concrete points, not `∀ x`. Proving them for
arbitrary `x : R*` is real, currently-undone work — see the file-end note.
-/

open Hypers

namespace Hypers.HyperLists.Probes.Derivatives

/-- The forward-difference algebraic derivative: `∂f(x) = (f(x+ε) - f(x)) / ε`,
    computed as `(f(x+ε) - f(x)) * ω` since `ε⁻¹ = ω`. -/
def deriv (f : R* → R*) (x : R*) : R* := (f (x + ε) - f x) * ω

/-- Central-difference variant, used below to recover the Readme's
    `δ := ω₀ / 2` definition of the algebraic Dirac delta. -/
def cderiv (f : R* → R*) (x : R*) : R* := (f (x + ε) - f (x - ε)) * ω * embedQ (1 / 2)

-- ═══════════════════════════════════════════════════════════════════════════
-- Polynomial derivative: ∂(x²) = 2x + ε, at concrete points.
-- ═══════════════════════════════════════════════════════════════════════════

def poly2 (y : R*) : R* := y * y

example : deriv poly2 (embedQ 3) = embedQ 6 + ε := by native_decide
example : deriv poly2 (embedQ 5) = embedQ 10 + ε := by native_decide
example : deriv poly2 (embedQ (-2)) = embedQ (-4) + ε := by native_decide
example : st (deriv poly2 (embedQ 3)) = 6 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Heaviside step H(x) := x > 0, and its algebraic derivative at 0.
-- Matches the Readme's `∂(x›0)(ε) = ω` claim (evaluated here at 0, where the
-- jump actually sits, rather than at ε — H is already constant on (0, ∞)).
-- ═══════════════════════════════════════════════════════════════════════════

def H (x : R*) : R* := if 0 < x then 1 else 0

example : H (ε : R*) = 1 := by native_decide
example : H (-ε : R*) = 0 := by native_decide
example : H (0 : R*) = 0 := by native_decide

/-- Forward difference: the step jumps by 1 over a step of ε, so the
    derivative is exactly `ω` — an algebraic Dirac delta with no limit. -/
example : deriv H 0 = ω := by native_decide

/-- Central difference straddles the jump symmetrically, halving it — this is
    the Readme's `δ := ω₀ / 2` definition of the algebraic Dirac delta,
    reached here as a genuine derivative rather than posited directly. -/
example : cderiv H 0 = ω * embedQ (1 / 2) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Spike δ₀(x) := (x = 0), the indicator at a single point.
-- ═══════════════════════════════════════════════════════════════════════════

def spike (x : R*) : R* := if x = 0 then 1 else 0

/-- Forward difference from the spike's peak falls to 0, giving `-ω` — the
    sign is a convention artifact of `deriv` being one-sided (Readme's
    `∂(x==0)(0) = ω` implicitly reads the *magnitude*; `cderiv` below is
    sign-symmetric and gives `0`, since the spike is even around 0). -/
example : deriv spike 0 = -ω := by native_decide
example : cderiv spike 0 = 0 := by native_decide

end Hypers.HyperLists.Probes.Derivatives

/-!
### What's still missing for the *general* (∀ x) versions

`deriv poly2 x = 2x + ε` is only checked above at three concrete `x`, not
proved for all `x : R*` — `native_decide` can't discharge a goal with a free
variable, and a real proof would need to unfold `poly2`, `merge`/`fieldMul`
on a symbolic `x`, and push through `coeffAt`-style reasoning the way
`Hyper/HyperList.lean`'s Field-instance proofs do. That's a natural next
probe (`∀ x, deriv poly2 x = 2 * x + ε`, then generalizing to arbitrary
polynomials), not attempted here.
-/
