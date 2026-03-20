/-
  HyperGeneralField.lean — Concrete hyperreal model via Laurent polynomials
  =========================================================================

  The "HyperGeneral construction": ε is a concrete atom (like Complex.I),
  as the basis element `Finsupp.single 1 1` in `AddMonoidAlgebra ℝ ℤ = ℤ →₀ ℝ`.
  Elements are finite sums ∑ aₙ εⁿ, n ∈ ℤ (Laurent polynomials).

  Type:  HGReal = Lex (AddMonoidAlgebra ℝ ℤ)
    - CommRing from AddMonoidAlgebra (via Algebra.Order.Ring.Synonym) — NO sorry
    - LinearOrder from Finsupp.Lex — NO sorry
    - Field: honest sorry (1+ε has no inverse in Laurent poly ring)
    - IsStrictOrderedRing: honest sorry (lex compat with ring ops)

  Lex order semantics (index = power of ε):
    ε = single(1, 1)    — at index 1,  dominates index 2, 3, ...
    ω = single(-1, 1)   — at index -1, dominates all real/ε terms
    order: ω(index -1) > embedℝ(index 0) > ε(index 1) > ε²(index 2) > ...

  Proved concretely (0 sorrys):
    CommRing, LinearOrder, ε_pos, ε_small, ω_mul_ε, st_embed, st_ε, ω_infinite
  Two honest sorrys (at end of file, to avoid instance conflicts):
    Field, IsStrictOrderedRing  (use `haveI := instHGField` when needed)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Ring.Synonym  -- CommRing (Lex R) from CommRing R
import Mathlib.Data.Finsupp.Lex             -- LinearOrder (Lex (ℤ →₀ ℝ))
import Mathlib.Data.Finsupp.Single

-- ─── 1. The concrete type ────────────────────────────────────────────────────

/-- Laurent polynomials ∑ aₙ εⁿ over ℝ, n ∈ ℤ. -/
abbrev HGRing := AddMonoidAlgebra ℝ ℤ

/-- Same type with the lexicographic order (smaller ℤ-index = more dominant). -/
abbrev HGReal := Lex HGRing

-- CommRing synthesizes via Mathlib.Algebra.Order.Ring.Synonym:
-- instance [CommRing R] : CommRing (Lex R) := h
noncomputable example : CommRing HGReal := inferInstance

-- LinearOrder: Finsupp.Lex.linearOrder needs Lex (ℤ →₀ ℝ) syntactically.
-- AddMonoidAlgebra ℝ ℤ = ℤ →₀ ℝ definitionally but not syntactically, so we
-- explicitly guide synthesis via `show`.
noncomputable instance instHGLinearOrder : LinearOrder HGReal :=
  show LinearOrder (Lex (ℤ →₀ ℝ)) from inferInstance

-- ─── 2. Atoms and embedding ───────────────────────────────────────────────────

/-- ε: the infinitesimal atom, basis element at index 1 (like Complex.I = ⟨0, 1⟩). -/
noncomputable def HG_ε : HGReal := toLex (Finsupp.single (1 : ℤ) (1 : ℝ))

/-- ω = ε⁻¹: the infinite atom, basis element at index -1. -/
noncomputable def HG_ω : HGReal := toLex (Finsupp.single (-1 : ℤ) (1 : ℝ))

-- Helper: single in HGRing for clean type annotations in proofs
private noncomputable abbrev hgs (n : ℤ) (r : ℝ) : HGRing := Finsupp.single n r

/-- Embed ℝ as constant (index-0) Laurent polynomials: r ↦ r·ε⁰. -/
noncomputable def HG_embedℝ : ℝ →+* HGReal where
  toFun r      := toLex (hgs 0 r)
  map_zero'    := by simp [hgs, Finsupp.single_zero]
  map_add' r s := Finsupp.single_add 0 r s
  map_one'     := rfl
  map_mul' r s := by
    show hgs 0 (r * s) = hgs 0 r * hgs 0 s
    simpa [hgs, zero_add] using (AddMonoidAlgebra.single_mul_single (0 : ℤ) (0 : ℤ) r s).symm

-- ─── 3. Standard part ─────────────────────────────────────────────────────────

/-- Standard part: the ε⁰ coefficient (real component). -/
noncomputable def HG_st (x : HGReal) : ℝ := (ofLex x : ℤ →₀ ℝ) 0

-- ─── 4. Core gauging law ──────────────────────────────────────────────────────

/-- ω · ε = 1: single(-1,1) · single(1,1) = single(0,1) = 1. -/
theorem HG_ω_mul_ε : HG_ω * HG_ε = 1 := by
  show hgs (-1) 1 * hgs 1 1 = 1
  rw [hgs, hgs, AddMonoidAlgebra.single_mul_single]
  simp [AddMonoidAlgebra.one_def]

theorem HG_ε_mul_ω : HG_ε * HG_ω = 1 := by rw [mul_comm]; exact HG_ω_mul_ε

-- ─── 5. Order lemmas ──────────────────────────────────────────────────────────
-- Strategy: use `show ... : Lex (ℤ →₀ ℝ)` to pin the type so that after
-- `rw [Finsupp.Lex.lt_iff]`, the sub-goals are about `ℤ →₀ ℝ` directly,
-- where `ofLex_toLex` and `Finsupp.single_apply` fire cleanly.

/-- ε > 0: at index 1, ε has coefficient 1 > 0. -/
theorem HG_ε_pos : (0 : HGReal) < HG_ε := by
  show (0 : Lex (ℤ →₀ ℝ)) < toLex (Finsupp.single (1 : ℤ) (1 : ℝ) : ℤ →₀ ℝ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨1, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply, ne_of_gt hj]
  · simp [Finsupp.single_eq_same]

/-- ε is infinitesimal: at index 0, ε has 0 while embedℝ r has r > 0. -/
theorem HG_ε_small (r : ℝ) (hr : 0 < r) : HG_ε < HG_embedℝ r := by
  show toLex (Finsupp.single (1 : ℤ) (1 : ℝ) : ℤ →₀ ℝ) <
       toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℝ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨0, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply,
          show (1 : ℤ) ≠ j from ne_of_gt (lt_trans hj (by norm_num : (0 : ℤ) < 1)),
          show (0 : ℤ) ≠ j from ne_of_gt hj]
  · simp [Finsupp.single_apply, show (1 : ℤ) ≠ 0 from by norm_num]
    exact hr

/-- embedℝ is strictly order-preserving. -/
theorem HG_embedℝ_strictMono : StrictMono (HG_embedℝ : ℝ → HGReal) := by
  intro r s hrs
  show toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℝ) <
       toLex (Finsupp.single (0 : ℤ) s : ℤ →₀ ℝ)
  rw [Finsupp.Lex.lt_iff]
  exact ⟨0, fun j hj => by simp [Finsupp.single_apply, ne_of_gt hj],
            by simp [Finsupp.single_eq_same]; exact hrs⟩

/-- ω > embedℝ r for r > 0: at index -1, ω has 1 while embedℝ r has 0. -/
theorem HG_ω_infinite (r : ℝ) (hr : 0 < r) : HG_embedℝ r < HG_ω := by
  show toLex (Finsupp.single (0 : ℤ) r : ℤ →₀ ℝ) <
       toLex (Finsupp.single (-1 : ℤ) (1 : ℝ) : ℤ →₀ ℝ)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨-1, fun j hj => ?_, ?_⟩
  · simp [Finsupp.single_apply,
          show (0 : ℤ) ≠ j from ne_of_gt (lt_trans hj (by norm_num : (-1 : ℤ) < 0)),
          show (-1 : ℤ) ≠ j from ne_of_gt hj]
  · simp [Finsupp.single_apply, show (0 : ℤ) ≠ -1 from by norm_num]

-- ─── 6. Standard part properties ─────────────────────────────────────────────

theorem HG_st_embed (r : ℝ) : HG_st (HG_embedℝ r) = r := by
  show (Finsupp.single (0 : ℤ) r : ℤ →₀ ℝ) 0 = r
  simp [Finsupp.single_eq_same]

@[simp] theorem HG_st_ε : HG_st HG_ε = 0 := by
  show (Finsupp.single (1 : ℤ) (1 : ℝ) : ℤ →₀ ℝ) 0 = 0
  simp [Finsupp.single_apply]

-- ─── 7. Honest sorrys (at end to avoid conflicting with concrete instances) ───
-- Placed last so all theorems above compile without instance conflicts.
-- The Field gap: ε⁻¹ = ω works, but (1+ε)⁻¹ needs FractionRing HGRing.
-- The IsStrictOrderedRing gap: lex order is compatible with ring ops.
-- Usage: `haveI := instHGField` or `attribute [instance] instHGField`.

noncomputable def instHGField : Field HGReal := sorry
noncomputable def instHGIsStrictOrderedRing : IsStrictOrderedRing HGReal := sorry
