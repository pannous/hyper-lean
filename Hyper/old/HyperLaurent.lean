/-
  HyperLaurent.lean — Hyperreal model via Laurent series (Hahn series over ℤ)
  =============================================================================

  Key insight: Laurent SERIES (unlike Laurent POLYNOMIALS) form a true FIELD.
  The element 1/(1+ε) = 1 - ε + ε² - ε³ + ... exists — it has infinitely many
  terms but its support is bounded below (well-ordered), which is exactly the
  Hahn series condition.

  Type:  HSReal = Lex (LaurentSeries ℝ) = Lex (HahnSeries ℤ ℝ)
    - Field: from Mathlib's HahnSeries.instField — 0 sorry
    - LinearOrder: from Mathlib's Lex order — 0 sorry
    - Not computable (#eval won't work — use HyperGeneral for that)

  Trade-off vs HyperGeneralField.lean (Laurent polynomials):
    Laurent poly: computable, CommRing, but NOT Field (no (1+ε)⁻¹)
    Laurent series: noncomputable, Field, exact inverses exist
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Summable  -- Field instance
import Mathlib.RingTheory.HahnSeries.Lex        -- LinearOrder on Lex
import Mathlib.Algebra.Field.Basic               -- Field (Lex K)
import Mathlib.Algebra.Order.Ring.Synonym        -- CommRing (Lex R)
import Mathlib.Tactic.Ring

open HahnSeries

-- ─── 1. The type ────────────────────────────────────────────────────────────

/-- Laurent series over ℝ with ℤ-indexed coefficients. -/
abbrev HSRing := LaurentSeries ℝ  -- = HahnSeries ℤ ℝ

/-- Hyperreal-like ordered field: Laurent series with lexicographic order. -/
abbrev HSReal := Lex HSRing

-- ─── 2. Field and LinearOrder: both from Mathlib, 0 sorry ──────────────────

noncomputable instance : Field HSReal := inferInstance
noncomputable instance instHSLinearOrder : LinearOrder HSReal :=
  show LinearOrder (Lex (HahnSeries ℤ ℝ)) from inferInstance

-- ─── 3. Atoms and embedding ────────────────────────────────────────────────

/-- ε: the canonical infinitesimal, coefficient 1 at index 1. -/
noncomputable def HS_ε : HSReal := toLex (single 1 (1 : ℝ))

/-- ω: the canonical infinite, coefficient 1 at index -1. -/
noncomputable def HS_ω : HSReal := toLex (single (-1) (1 : ℝ))

/-- Embed ℝ as constant series (index 0). -/
noncomputable def HS_embedℝ (r : ℝ) : HSReal := toLex (single 0 r)

-- ─── 4. Core gauging law ───────────────────────────────────────────────────

/-- ω · ε = 1: the fundamental gauging relation. -/
theorem HS_ω_mul_ε : HS_ω * HS_ε = 1 := by
  show toLex (single (-1 : ℤ) (1 : ℝ) * single 1 1) = 1
  rw [single_mul_single, show (-1 : ℤ) + 1 = 0 by norm_num, one_mul, single_zero_one]; rfl

theorem HS_ε_mul_ω : HS_ε * HS_ω = 1 := by rw [mul_comm]; exact HS_ω_mul_ε

-- ─── 5. The key advantage: exact inverses ──────────────────────────────────

/-- (1+ε) ≠ 0 — needed for field inverse. -/
theorem HS_one_add_ε_ne_zero : (1 : HSReal) + HS_ε ≠ 0 := by
  intro h
  have : (ofLex (1 + HS_ε : HSReal) : HSRing).coeff 0 = 0 := by
    simp [h]
  simp [HS_ε, coeff_single_of_ne (show (1 : ℤ) ≠ 0 by norm_num), coeff_one] at this

/-- (1+ε)⁻¹ exists and satisfies the exact field inverse law.
    In Laurent series, 1/(1+ε) = 1 - ε + ε² - ε³ + ... is a well-defined element. -/
theorem HS_one_add_ε_mul_inv : (1 + HS_ε) * (1 + HS_ε)⁻¹ = 1 :=
  mul_inv_cancel₀ HS_one_add_ε_ne_zero

-- ─── 6. Standard part ─────────────────────────────────────────────────────

/-- Standard part: the coefficient at index 0. -/
noncomputable def HS_st (x : HSReal) : ℝ := (ofLex x : HSRing).coeff 0

theorem HS_st_embed (r : ℝ) : HS_st (HS_embedℝ r) = r := by
  simp [HS_st, HS_embedℝ, coeff_single_same]

@[simp] theorem HS_st_ε : HS_st HS_ε = 0 := by
  simp [HS_st, HS_ε, coeff_single_of_ne (show (1 : ℤ) ≠ 0 by norm_num)]

-- ─── 7. Order lemmas ──────────────────────────────────────────────────────

/-- ε > 0. -/
theorem HS_ε_pos : (0 : HSReal) < HS_ε := by
  show (0 : Lex (HahnSeries ℤ ℝ)) < toLex (single (1 : ℤ) (1 : ℝ))
  rw [HahnSeries.lt_iff]
  exact ⟨1,
    fun j hj => by simp [coeff_single_of_ne (ne_of_lt hj)],
    by simp [coeff_single_same]⟩

/-- ε < r for any positive real r: ε is infinitesimal. -/
theorem HS_ε_small (r : ℝ) (hr : 0 < r) : HS_ε < HS_embedℝ r := by
  show toLex (single (1 : ℤ) (1 : ℝ)) < toLex (single (0 : ℤ) r)
  rw [HahnSeries.lt_iff]
  refine ⟨0, fun j hj => ?_, ?_⟩
  · simp [coeff_single_of_ne (by omega : j ≠ 1), coeff_single_of_ne (by omega : j ≠ 0)]
  · simp [coeff_single_same, coeff_single_of_ne (show (1 : ℤ) ≠ 0 by norm_num)]
    exact hr

-- ─── 8. Embedding from Laurent polynomials ─────────────────────────────────
-- HyperGeneralField's HGReal (Laurent poly) embeds into HSReal (Laurent series)
-- via the natural inclusion of finitely-supported functions into Hahn series.
-- This is the "computation meets proof" bridge: compute in HGReal, prove in HSReal.
