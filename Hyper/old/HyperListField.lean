/-
  HyperListField.lean — experiment: ℚ-based sibling of HyperGeneralField.lean
  ============================================================================

  HyperList.lean represents R* = ∑ aₙ εⁿ as a raw `List (ℚ × ℚ)` with a
  hand-written `simplify`/`merge` for canonical form, then tries to prove a
  full `Field R*` instance on top of that list representation — requiring
  `add_assoc`, `mul_comm`, etc. to be proved from scratch, and ~24 of those
  are still `sorry`.

  This file explores an alternative representation for the *same* idea
  (Laurent polynomials ∑ aₙ εⁿ, n ∈ ℤ), following HyperGeneralField.lean's
  approach for the ℝ case but with ℚ coefficients (matching HyperList's
  choice of ℚ over ℝ for decidability): `Lex (AddMonoidAlgebra ℚ ℤ)`.
  CommRing and LinearOrder come for free via `inferInstance`, because
  Mathlib already has those proofs for AddMonoidAlgebra / Finsupp.Lex.

  As in HyperGeneralField.lean, a full `Field` instance is NOT attempted:
  Laurent polynomials are not a field (1+ε has no polynomial inverse; you'd
  need a formal Laurent-series/Hahn-series completion). That is an honest
  limitation of this representation, not a missing proof.

  Standalone experiment: does not touch or import HyperList.lean.
-/
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Ring.Synonym  -- CommRing (Lex R) from CommRing R
import Mathlib.Data.Finsupp.Lex             -- LinearOrder (Lex (ℤ →₀ ℚ))
import Mathlib.Data.Finsupp.Single
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

-- ─── 1. The concrete type ──────────────────────

/-- Laurent polynomials ∑ aₙ εⁿ over ℚ, n ∈ ℤ. -/
abbrev HLRing := AddMonoidAlgebra ℚ ℤ

/-- Same type with the lexicographic order (smaller ℤ-index = more dominant). -/
abbrev HLReal := Lex HLRing

-- CommRing synthesizes via Mathlib.Algebra.Order.Ring.Synonym:
-- instance [CommRing R] : CommRing (Lex R) := h
noncomputable example : CommRing HLReal := inferInstance

-- LinearOrder: Finsupp.Lex.linearOrder needs Lex (ℤ →₀ ℚ) syntactically.
-- AddMonoidAlgebra ℚ ℤ = ℤ →₀ ℚ definitionally but not syntactically, so we
-- explicitly guide synthesis via `show`.
noncomputable instance instHLLinearOrder : LinearOrder HLReal :=
  show LinearOrder (Lex (ℤ →₀ ℚ)) from inferInstance

-- ─── 2. Atoms and embedding ─────────────────────

/-- ε: the infinitesimal atom, basis element at index 1 (like Complex.I = ⟨0, 1⟩). -/
noncomputable def HL_ε : HLReal := toLex (Finsupp.single (1 : ℤ) (1 : ℚ))

/-- ω = ε⁻¹: the infinite atom, basis element at index -1. -/
noncomputable def HL_ω : HLReal := toLex (Finsupp.single (-1 : ℤ) (1 : ℚ))

-- Helper: single in HLRing for clean type annotations in proofs
private noncomputable abbrev hls (n : ℤ) (r : ℚ) : HLRing := Finsupp.single n r

/-- Embed ℚ as constant (index-0) Laurent polynomials: r ↦ r·ε⁰. -/
noncomputable def HL_embedQ : ℚ →+* HLReal where
  toFun r      := toLex (hls 0 r)
  map_zero'    := by simp [hls, Finsupp.single_zero]
  map_add' r s := Finsupp.single_add 0 r s
  map_one'     := rfl
  map_mul' r s := by
    show hls 0 (r * s) = hls 0 r * hls 0 s
    simpa [hls, zero_add] using (AddMonoidAlgebra.single_mul_single (0 : ℤ) (0 : ℤ) r s).symm

-- ─── 3. Standard part ────────────────────────

/-- Standard part: the ε⁰ coefficient (rational component). -/
def HL_st (x : HLReal) : ℚ := (ofLex x : ℤ →₀ ℚ) 0

-- ─── 4. Core gauging law ────────────────────────

/-- ω · ε = 1: single(-1,1) · single(1,1) = single(0,1) = 1. -/
theorem HL_ω_mul_ε : HL_ω * HL_ε = 1 := by
  show hls (-1) 1 * hls 1 1 = 1
  rw [hls, hls, AddMonoidAlgebra.single_mul_single]
  simp [AddMonoidAlgebra.one_def]

theorem HL_ε_mul_ω : HL_ε * HL_ω = 1 := by rw [mul_comm]; exact HL_ω_mul_ε

-- ─── 5. Order lemmas ─────────────────────────
-- Strategy: use `show ... : Lex (ℤ →₀ ℚ)` to pin the type so that after
-- `rw [Finsupp.Lex.lt_iff]`, the sub-goals are about `ℤ →₀ ℚ` directly,
-- where `ofLex_toLex` and `Finsupp.single_apply` fire cleanly.

/-- ε > 0: at index 1, ε has coefficient 1 > 0. -/
theorem HL_ε_pos : (0 : HLReal) < HL_ε := by
  show (0 : Lex (ℤ →₀ ℚ)) < toLex (Finsupp.single (1 : ℤ) (1 : ℚ) : ℤ →₀ ℚ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨1, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply, ne_of_gt hj]
  · simp [Finsupp.single_eq_same]

/-- ε is infinitesimal: at index 0, ε has 0 while embedQ r has r > 0. -/
theorem HL_ε_small (r : ℚ) (hr : 0 < r) : HL_ε < HL_embedQ r := by
  show toLex (Finsupp.single (1 : ℤ) (1 : ℚ) : ℤ →₀ ℚ) <
       toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℚ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨0, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply,
          show (1 : ℤ) ≠ j from ne_of_gt (lt_trans hj (by norm_num : (0 : ℤ) < 1)),
          show (0 : ℤ) ≠ j from ne_of_gt hj]
  · simp [Finsupp.single_apply, show (1 : ℤ) ≠ 0 from by norm_num]
    exact hr

/-- ε < 1 (specialize HL_ε_small at r = 1). -/
theorem HL_ε_lt_one : HL_ε < (1 : HLReal) := by
  have h := HL_ε_small 1 (by norm_num)
  simpa [HL_embedQ, hls] using h

/-- embedQ is strictly order-preserving. -/
theorem HL_embedQ_strictMono : StrictMono (HL_embedQ : ℚ → HLReal) := by
  intro r s hrs
  show toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℚ) <
       toLex (Finsupp.single (0 : ℤ) s : ℤ →₀ ℚ)
  rw [Finsupp.Lex.lt_iff]
  exact ⟨0, fun j hj => by simp [Finsupp.single_apply, ne_of_gt hj],
            by simp [Finsupp.single_eq_same]; exact hrs⟩

/-- ω > embedQ r for r > 0: at index -1, ω has 1 while embedQ r has 0. -/
theorem HL_ω_infinite (r : ℚ) (hr : 0 < r) : HL_embedQ r < HL_ω := by
  show toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℚ) <
       toLex (Finsupp.single (-1 : ℤ) (1 : ℚ) : ℤ →₀ ℚ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨-1, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply,
          show (0 : ℤ) ≠ j from ne_of_gt (lt_trans hj (by norm_num : (-1 : ℤ) < 0)),
          show (-1 : ℤ) ≠ j from ne_of_gt hj]
  · simp [Finsupp.single_apply, show (0 : ℤ) ≠ -1 from by norm_num]

-- ─── 6. Standard part properties ──────────────────

theorem HL_st_embed (r : ℚ) : HL_st (HL_embedQ r) = r := by
  show (Finsupp.single (0 : ℤ) r : ℤ →₀ ℚ) 0 = r
  simp [Finsupp.single_eq_same]

@[simp] theorem HL_st_ε : HL_st HL_ε = 0 := by
  show (Finsupp.single (1 : ℤ) (1 : ℚ) : ℤ →₀ ℚ) 0 = 0
  simp [Finsupp.single_apply]

@[simp] theorem HL_st_ω : HL_st HL_ω = 0 := by
  show (Finsupp.single (-1 : ℤ) (1 : ℚ) : ℤ →₀ ℚ) 0 = 0
  simp [Finsupp.single_apply]

-- ─── 7. Honest limitation (documented, not attempted) ───────────────────────
-- A full `Field HLReal` (and `IsStrictOrderedRing HLReal`) instance is NOT
-- provable on this representation: Laurent polynomials have no inverse for
-- e.g. `1 + HL_ε` (that needs an infinite formal Laurent series). This
-- matches HyperGeneralField.lean's conclusion for the ℝ case. We deliberately
-- do not add `sorry`-laden Field/IsStrictOrderedRing instances here — CommRing
-- + LinearOrder + the concrete lemmas above are the honest, fully-proved
-- surface this representation supports.

-- ─── 8. Smoke checks matching HyperList.lean's native_decide facts ──────────

example : HL_ω * HL_ε = 1 := HL_ω_mul_ε
example : HL_ε * HL_ω = 1 := HL_ε_mul_ω
example : (0 : HLReal) < HL_ε := HL_ε_pos
example : HL_ε < (1 : HLReal) := HL_ε_lt_one
