/-
  Exact `1/(π+e)`: raw fraction arithmetic over PiEField.
  ===========================================================

  `Hyper/HyperApproxInv.lean` solves `R*`'s `1/(ε+ω)` via a truncated
  geometric series — sound there because `ε`'s higher powers are genuinely
  infinitesimal (`R*`'s own order structure). That trick does NOT apply to
  `PiEField`'s `1/(π+e)`: π and e are flat "order 0" generators, not
  infinitesimals, so `π/e` (needed to factor `π+e = e·(1+π/e)`) is just an
  ordinary-sized value, not a shrinking one — the geometric series wouldn't
  converge/improve. `1/(π+e)` needs a genuine field of fractions instead.

  ⚠️ Scope, stated plainly (this is the "quick" version, not the complete
  one): a fraction `(num, den)` has no canonical form — `(2,2)` and `(1,1)`
  are the same value, different pairs — so the correct equality is
  cross-multiplication (`eqv`), not raw structural `=`. Bundling that up as
  a genuine `Quotient`-based field TYPE (so ordinary `=` means the right
  thing, matching `Hyper.HyperList.HyperQuotient`'s precedent) needs
  transitivity of `eqv`, which needs `PiEField` proved to have no zero
  divisors first (standard leading-term argument, similar in shape to
  `HyperList.lean`'s own `lt_of_lead_pair`/`canonical_unique`-style order
  proofs) — real, tractable, but genuinely separate work, not attempted
  here. What's delivered instead: correct, `native_decide`-checked
  arithmetic and equality on individual concrete fractions via `eqv`
  directly — sound for every fact stated below, since checking one specific
  cross-multiplication doesn't need general transitivity, only that `eqv`
  correctly captures "same rational value", which it does by construction.

  Note: `Hyper/PiEField.lean` independently grew a more complete answer to
  the same question while this file was being built — `RatFun.eval`
  (returns `.value` for the sound Laurent-monomial fragment, `.symbolic`
  rather than a wrong answer otherwise) plus `RatFun.exactNormalize`, a
  *genuine* field of fractions via Mathlib's own `FractionRing (MvPolynomial
  (Fin 2) ℚ)` — architecturally the right long-term answer (real Field laws,
  not a hand-verified relation), at the cost of being `noncomputable`
  (`simp`/tactic-checked, not `native_decide`-checked). This file's `RFrac`
  stays as a simpler, fully computable cross-check that the underlying
  arithmetic is correct — not a replacement for that approach.
-/
import Hyper.PiEField

/-- A fraction `num/den` of two `PiEField` values. -/
abbrev RFrac := PiEField × PiEField

namespace RFrac

def add (x y : RFrac) : RFrac := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)
def neg (x : RFrac) : RFrac := (-x.1, x.2)
def sub (x y : RFrac) : RFrac := add x (neg y)
def mul (x y : RFrac) : RFrac := (x.1 * y.1, x.2 * y.2)
/-- Swap numerator and denominator — the standard field-of-fractions
    inverse; correct whenever `x.1 ≠ 0` (unattended for `x.1 = 0`, same
    "don't chase the ill-defined edge case" spirit as `R*`'s own `Inv`). -/
def inv (x : RFrac) : RFrac := (x.2, x.1)

instance : Add RFrac := ⟨add⟩
instance : Neg RFrac := ⟨neg⟩
instance : Sub RFrac := ⟨sub⟩
instance : Mul RFrac := ⟨mul⟩
instance : Inv RFrac := ⟨inv⟩
instance : One RFrac := ⟨(1, 1)⟩
instance : Zero RFrac := ⟨(0, 1)⟩

/-- The correct notion of equality for a fraction: cross-multiplication, not
    structural `=` of the `(num, den)` pair. Decidable directly — checking
    one concrete instance doesn't need `eqv` bundled as a formal
    `Equivalence`/`Setoid` (see file header). -/
def eqv (x y : RFrac) : Prop := x.1 * y.2 = y.1 * x.2
instance : HasEquiv RFrac := ⟨eqv⟩
instance (x y : RFrac) : Decidable (x ≈ y) :=
  inferInstanceAs (Decidable (x.1 * y.2 = y.1 * x.2))

open PiEField (piGen eGen)

def piPlusE : RFrac := (piGen + eGen, 1)

-- ═══════════════════════════════════════════════════════════════════════════
-- The actual ask: 1/(π+e) genuinely, exactly inverts π+e — not an
-- approximation, not truncated at some order.
-- ═══════════════════════════════════════════════════════════════════════════

example : piPlusE⁻¹ * piPlusE ≈ 1 := by native_decide
example : piPlusE * piPlusE⁻¹ ≈ 1 := by native_decide

-- Composes correctly with ordinary arithmetic: π/(π+e) · (π+e) = π.
example : ((piGen, 1) * piPlusE⁻¹ : RFrac) * piPlusE ≈ (piGen, 1) := by native_decide

end RFrac
