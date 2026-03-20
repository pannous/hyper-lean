/-
  Hyperreal-valued Probability Theory
  ====================================

  Standard measure theory assigns P({x}) = 0 to every singleton in a continuous
  distribution.  This is philosophically unsatisfying: hitting a specific point
  is "not impossible", yet has probability zero.

  Here we replace 0 with ε (a positive infinitesimal) so that:
    • P({x}) = ε        (positive, but smaller than any standard probability)
    • st(ε)  = 0        (standard part recovers classical theory)

  For the dart-disc problem (disc of radius R):
    • P({z}) = ε / (π · R²)

  Mathematical basis (gauging law):
    • The hyperreal [0,1] has ω = ε⁻¹ "points"
    • ω · ε = 1 ensures total mass normalises to 1

  Design: self-contained axiomatic sketch.
  LinearOrderedField was deprecated in Mathlib (2025-10-30);
  we use [Field] [LinearOrder] [IsStrictOrderedRing] instead.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory Set Metric

-- ─── 1. Hyperreal type with minimal axioms ───────────────────────────────────

/-- The type of hyperreal numbers (abstract). -/
axiom HReal : Type

noncomputable instance : Field HReal         := by sorry
noncomputable instance : LinearOrder HReal   := by sorry
noncomputable instance : IsStrictOrderedRing HReal := by sorry

/-- The standard embedding ℝ → HReal (ring homomorphism). -/
noncomputable axiom embedℝ : ℝ →+* HReal

noncomputable instance : Coe ℝ HReal := ⟨embedℝ⟩

/-- The embedding is strictly order-preserving. -/
axiom embedℝ_strictMono : StrictMono (embedℝ : ℝ → HReal)

/-- The positive infinitesimal. -/
noncomputable axiom ε : HReal

axiom ε_pos   : 0 < ε
axiom ε_small : ∀ r : ℝ, 0 < r → ε < embedℝ r

/-- Standard part (shadow map HReal → ℝ). -/
noncomputable axiom st : HReal → ℝ

axiom st_embed (r : ℝ) : st (embedℝ r) = r
@[simp] axiom st_ε : st ε = 0

/-- ω = ε⁻¹  (the infinite counterpart of ε). -/
noncomputable def ω : HReal := ε⁻¹

-- ─── 2. Gauging law: ω · ε = 1 ───────────────────────────────────────────────

theorem ω_mul_ε : ω * ε = 1 :=
  inv_mul_cancel₀ (ne_of_gt ε_pos)

theorem ε_mul_ω : ε * ω = 1 := by rw [mul_comm]; exact ω_mul_ε

/-- ω exceeds every standard positive real.
    Proof: ε < embedℝ(1/r), so ε⁻¹ > embedℝ(r). -/
theorem ω_infinite (r : ℝ) (hr : 0 < r) : embedℝ r < ω := by
  rw [ω]
  -- ε < embedℝ (1/r), so (embedℝ (1/r))⁻¹ < ε⁻¹, i.e. embedℝ r < ε⁻¹
  sorry

-- ─── 3. Hyperreal-valued finitely-additive measure ───────────────────────────

/-- A finitely-additive measure valued in HReal.
    Carrier structure for hyperreal probability. -/
structure HyperMeasure (α : Type*) [MeasurableSpace α] where
  toFun    : Set α → HReal
  empty    : toFun ∅ = 0
  nonneg   : ∀ s, 0 ≤ toFun s
  additive : ∀ s t : Set α, Disjoint s t → MeasurableSet s → MeasurableSet t →
               toFun (s ∪ t) = toFun s + toFun t

-- ─── 4. Hyperreal uniform measure on ℝ (1-D) ─────────────────────────────────

/-- The hyperreal uniform measure on ℝ. -/
axiom hyperUniform₁ : HyperMeasure ℝ

/-- Every singleton in ℝ gets mass ε. -/
axiom hyperUniform₁_singleton (x : ℝ) : hyperUniform₁.toFun {x} = ε

/-- The unit interval [0,1] has total mass 1
    (it contains ω atoms of mass ε, and ω · ε = 1).
    Full proof requires Loeb measure theory. -/
axiom hyperUniform₁_unit : hyperUniform₁.toFun (Icc 0 1) = 1

-- ─── 5. Hyperreal uniform measure on ℂ (2-D disc) ───────────────────────────

/-- Atom mass for a disc of radius R: each singleton gets ε/(πR²). -/
noncomputable def discAtomMass (R : ℝ) : HReal :=
  ε / embedℝ (Real.pi * R ^ 2)

/-- The hyperreal uniform measure on the open disc of radius R centred at 0. -/
axiom hyperUniform_disc (R : ℝ) (hR : 0 < R) : HyperMeasure ℂ

/-- Every point in the disc gets probability ε/(πR²). -/
axiom hyperUniform_disc_singleton (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (hyperUniform_disc R hR).toFun {z} = discAtomMass R

/-- Total disc mass = 1  (follows from ω · ε = 1 after scaling by 1/(πR²)).
    Full proof uses 2-D Loeb measure. -/
axiom hyperUniform_disc_total (R : ℝ) (hR : 0 < R) :
    (hyperUniform_disc R hR).toFun (ball (0 : ℂ) R) = 1

-- ─── 6. Dart theorem ─────────────────────────────────────────────────────────

/-- The hyperreal probability of hitting a specific point z in a disc of radius R. -/
theorem dart_hyperprob_singleton (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (hyperUniform_disc R hR).toFun {z} = ε / embedℝ (Real.pi * R ^ 2) :=
  hyperUniform_disc_singleton R hR z

/-- That probability is strictly positive — the event is *possible* (unlike classical theory). -/
theorem dart_hyperprob_pos (R : ℝ) (hR : 0 < R) (z : ℂ) :
    0 < (hyperUniform_disc R hR).toFun {z} := by
  rw [dart_hyperprob_singleton]
  apply div_pos ε_pos
  have hpos : (0 : ℝ) < Real.pi * R ^ 2 := mul_pos Real.pi_pos (pow_pos hR 2)
  have h := embedℝ_strictMono hpos
  rwa [embedℝ.map_zero] at h

/-- The standard part recovers the classical result 0.
    (sorry: ε/(πR²) is infinitesimal, so st = 0; provable from ε_small and field axioms.) -/
theorem dart_hyperprob_st_zero (R : ℝ) (hR : 0 < R) (z : ℂ) :
    st ((hyperUniform_disc R hR).toFun {z}) = 0 := by
  rw [dart_hyperprob_singleton]; sorry

-- ─── 7. Key examples and the three-theory spectrum ───────────────────────────
--
--   Classical (Lebesgue): P({z}) = 0
--   Hyperreal:            P({z}) = ε  (positive infinitesimal)
--   Dirac:                P({z}) = 1  (certainty; all mass at one atom)
--
-- Hyperreal is the "middle ground":
--   ε > 0 (the event can happen)
--   st(ε) = 0 (recovers Lebesgue theory)

-- 1-D singleton has positive mass:
example (x : ℝ) : 0 < hyperUniform₁.toFun {x} := by
  rw [hyperUniform₁_singleton]; exact ε_pos

-- … whose standard part is zero:
example (x : ℝ) : st (hyperUniform₁.toFun {x}) = 0 := by
  rw [hyperUniform₁_singleton]; exact st_ε

-- Dart-disc probability is below any standard positive threshold:
-- Proof: ε/(πR²) < embedℝ p  ↔  ε < embedℝ(πR²) * embedℝ p = embedℝ(πR²·p)
--        which follows from ε_small since πR²·p > 0.
theorem dart_hyperprob_infinitesimal (R : ℝ) (hR : 0 < R) (z : ℂ) (p : ℝ) (hp : 0 < p) :
    (hyperUniform_disc R hR).toFun {z} < embedℝ p := by
  simp only [dart_hyperprob_singleton]
  have hc : (0 : ℝ) < Real.pi * R ^ 2 := mul_pos Real.pi_pos (pow_pos hR 2)
  have hcH : (0 : HReal) < embedℝ (Real.pi * R ^ 2) := by
    have := embedℝ_strictMono hc; rwa [embedℝ.map_zero] at this
  rw [div_lt_iff₀ hcH, ← embedℝ.map_mul]
  exact ε_small _ (mul_pos hp hc)
