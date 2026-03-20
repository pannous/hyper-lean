/-
  Stochastic concepts in Lean 4 / Mathlib
  =========================================
  Demonstrates: null sets, probability-0 events, almost-everywhere (a.e.),
  probability measures, and the "a.e. ↔ probability 1" equivalence.
-/
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE

open MeasureTheory

-- ─── 1. API surface check ────────────────────────────────────────────────────

-- Null-measurable sets (approximated up to a null set)
#check @NullMeasurableSet

-- Almost-everywhere filter: s ∈ ae μ  ↔  μ sᶜ = 0
#check @MeasureTheory.ae
#check @mem_ae_iff          -- s ∈ ae μ ↔ μ sᶜ = 0
#check @ae_iff              -- (∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0

-- Probability measure typeclass: μ univ = 1
#check @IsProbabilityMeasure
#check @IsProbabilityMeasure.measure_univ

-- ae ↔ prob 1 (for measurable sets under a probability measure)
#check @mem_ae_iff_prob_eq_one   -- s ∈ ae μ ↔ μ s = 1
#check @ae_iff_prob_eq_one       -- (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1

-- ─── 2. Dirac measure is a probability measure ────────────────────────────────

-- The Dirac measure δ_x concentrates all mass on the single point x.
-- Mathlib provides the IsProbabilityMeasure instance automatically.
example : IsProbabilityMeasure (Measure.dirac (0 : ℕ)) :=
  inferInstance

-- ─── 3. Null set (measure-zero set) ──────────────────────────────────────────

-- Under δ₀, any set not containing 0 has measure zero.
example : Measure.dirac (0 : ℕ) {1} = 0 := by
  simp

-- The empty set always has measure zero.
example (μ : Measure ℕ) : μ ∅ = 0 :=
  measure_empty

-- ─── 4. Almost-everywhere notation ───────────────────────────────────────────

-- Under δ₀, the predicate "x = 0" holds almost everywhere.
-- ae_dirac_eq shows ae (dirac a) = pure a, so we just need p a.
example : ∀ᵐ x ∂(Measure.dirac (0 : ℕ)), x = 0 := by
  simp [ae_dirac_eq]

-- Two functions equal a.e. under δ_a iff they agree at a.
example (a : ℕ) (f g : ℕ → ℕ) (h : f a = g a) :
    f =ᵐ[Measure.dirac a] g := by
  simp [Filter.EventuallyEq, ae_dirac_eq, h]

-- ─── 5. Probability 1 ↔ Almost Everywhere ────────────────────────────────────

-- For a probability measure and a measurable set, being a.e.-full is the same
-- as having probability 1.
example (μ : Measure ℕ) [IsProbabilityMeasure μ] (s : Set ℕ) (hs : MeasurableSet s) :
    s ∈ MeasureTheory.ae μ ↔ μ s = 1 :=
  mem_ae_iff_prob_eq_one hs

-- ─── 6. ae_iff spelled out ────────────────────────────────────────────────────

-- A predicate holds a.e. iff the exceptional set has measure zero.
example (μ : Measure ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∀ᵐ x ∂μ, p x) ↔ μ {x | ¬p x} = 0 :=
  ae_iff
