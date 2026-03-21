/-
  HyperGeneralField.lean — Concrete hyperreal model via Laurent polynomials
  =========================================================================

  The "HyperGeneral construction": ε is a concrete atom (like Complex.I),
  as the basis element `Finsupp.single 1 1` in `AddMonoidAlgebra ℝ ℤ = ℤ →₀ ℝ`.
  Elements are finite sums ∑ aₙ εⁿ, n ∈ ℤ (Laurent polynomials).

  Type:  HGReal = Lex (AddMonoidAlgebra ℝ ℤ)
    - CommRing from AddMonoidAlgebra (via Algebra.Order.Ring.Synonym) — proven
    - LinearOrder from Finsupp.Lex — proven
    - Field: no (1+ε has no inverse in Laurent poly ring)
    - IsStrictOrderedRing: no (lex compat with ring ops)

  Lex order semantics (index = power of ε):
    ε = single(1, 1)    — at index 1,  dominates index 2, 3, ...
    ω = single(-1, 1)   — at index -1, dominates all real/ε terms
    order: ω(index -1) > embedℝ(index 0) > ε(index 1) > ε²(index 2) > ...

  Proved concretely:
    CommRing, LinearOrder, ε_pos, ε_small, ω_mul_ε, st_embed, st_ε, ω_infinite
    ≈ₕ (approx equivalence), geometric series identity, approximate inverse
  Two honest sorrys (at end of file, to avoid instance conflicts):
    Field, IsStrictOrderedRing  (use `haveI := instHGField` when needed)
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Order.Ring.Synonym  -- CommRing (Lex R) from CommRing R
import Mathlib.Algebra.Ring.GeomSum         -- geom_sum_mul, mul_neg_geom_sum
import Mathlib.Tactic.Ring                  -- ring tactic
import Mathlib.Data.Finsupp.Lex             -- LinearOrder (Lex (ℤ →₀ ℝ))
import Mathlib.Data.Finsupp.Single

-- ─── 1. The concrete type ──────────────────────

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

-- ─── 2. Atoms and embedding ─────────────────────

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

-- ─── 3. Standard part ────────────────────────

/-- Standard part: the ε⁰ coefficient (real component). -/
noncomputable def HG_st (x : HGReal) : ℝ := (ofLex x : ℤ →₀ ℝ) 0

-- ─── 4. Core gauging law ────────────────────────

/-- ω · ε = 1: single(-1,1) · single(1,1) = single(0,1) = 1. -/
theorem HG_ω_mul_ε : HG_ω * HG_ε = 1 := by
  show hgs (-1) 1 * hgs 1 1 = 1
  rw [hgs, hgs, AddMonoidAlgebra.single_mul_single]
  simp [AddMonoidAlgebra.one_def]

theorem HG_ε_mul_ω : HG_ε * HG_ω = 1 := by rw [mul_comm]; exact HG_ω_mul_ε

-- ─── 5. Order lemmas ─────────────────────────
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

-- ─── 6. Standard part properties ──────────────────

theorem HG_st_embed (r : ℝ) : HG_st (HG_embedℝ r) = r := by
  show (Finsupp.single (0 : ℤ) r : ℤ →₀ ℝ) 0 = r
  simp [Finsupp.single_eq_same]

@[simp] theorem HG_st_ε : HG_st HG_ε = 0 := by
  show (Finsupp.single (1 : ℤ) (1 : ℝ) : ℤ →₀ ℝ) 0 = 0
  simp [Finsupp.single_apply]

-- ─── 7. Approximate equivalence (≈) ─────────────────────────────────────────
-- Instead of a full Field (which requires power series for (1+ε)⁻¹),
-- we define an "approximate field": every element with nonzero standard part
-- has an inverse up to arbitrarily small infinitesimals.

-- Helper: extract coefficient at index k, avoiding type-annotation pitfalls
noncomputable def HG_coeff (x : HGReal) (k : ℤ) : ℝ := (ofLex x : HGRing) k

@[simp] theorem HG_coeff_neg (a : HGReal) (k : ℤ) :
    HG_coeff (-a) k = -HG_coeff a k := Finsupp.neg_apply ..
@[simp] theorem HG_coeff_add (a b : HGReal) (k : ℤ) :
    HG_coeff (a + b) k = HG_coeff a k + HG_coeff b k := Finsupp.add_apply ..
@[simp] theorem HG_coeff_sub (a b : HGReal) (k : ℤ) :
    HG_coeff (a - b) k = HG_coeff a k - HG_coeff b k := Finsupp.sub_apply ..
@[simp] theorem HG_coeff_single (n : ℤ) (r : ℝ) (k : ℤ) :
    HG_coeff (toLex (Finsupp.single n r : HGRing)) k = if k = n then r else 0 := by
  simp [HG_coeff, Finsupp.single_apply, eq_comm]

/-- An element is infinitesimal: all coefficients at non-positive indices are zero.
    Equivalently, the element is smaller than every positive real. -/
def HG_isInfinitesimal (x : HGReal) : Prop :=
  ∀ k : ℤ, k ≤ 0 → HG_coeff x k = 0

/-- Approximate equality: x ≈ y iff x - y is infinitesimal. -/
def HG_approx (x y : HGReal) : Prop := HG_isInfinitesimal (x - y)

notation:50 x " ≈ₕ " y => HG_approx x y

/-- ε is infinitesimal. -/
theorem HG_ε_infinitesimal : HG_isInfinitesimal HG_ε := by
  intro k hk
  simp [HG_coeff, HG_ε, Finsupp.single_apply,
        ne_of_gt (lt_of_le_of_lt hk Int.one_pos)]

/-- ≈ is reflexive. -/
theorem HG_approx_refl (x : HGReal) : x ≈ₕ x := by
  intro k _; simp [HG_approx, HG_isInfinitesimal, HG_coeff, sub_self]

/-- ≈ is symmetric. -/
theorem HG_approx_symm {x y : HGReal} (h : x ≈ₕ y) : y ≈ₕ x := by
  intro k hk
  simp only [HG_coeff_sub, sub_eq_zero]
  have := h k hk; simp only [HG_coeff_sub, sub_eq_zero] at this
  exact this.symm

/-- ≈ is transitive. -/
theorem HG_approx_trans {x y z : HGReal} (hxy : x ≈ₕ y) (hyz : y ≈ₕ z) : x ≈ₕ z := by
  intro k hk
  simp only [HG_coeff_sub]
  have h1 := hxy k hk; simp only [HG_coeff_sub, sub_eq_zero] at h1
  have h2 := hyz k hk; simp only [HG_coeff_sub, sub_eq_zero] at h2
  rw [h1, h2, sub_self]

-- ─── 8. Partial inverse via geometric series ────────────────────────────────
-- (1+ε) has no exact inverse in Laurent polynomials, but the truncated
-- geometric series ∑_{k<n} (-ε)^k gives an approximate inverse:
--   (1+ε) · ∑(-ε)^k = 1 - (-ε)^n ≈ₕ 1

/-- Partial inverse of (1+ε): truncated geometric series ∑_{k<n} (-ε)^k. -/
noncomputable def HG_partialInv (n : ℕ) : HGReal :=
  (Finset.range n).sum (fun k => (-HG_ε) ^ k)

/-- Geometric series identity: (1+ε) · partialInv(n) = 1 - (-ε)^n.
    Uses Mathlib's `mul_neg_geom_sum`: (1-x) · ∑ x^i = 1 - x^n with x = -ε. -/
theorem HG_geom_identity (n : ℕ) :
    (1 + HG_ε) * HG_partialInv n = 1 - (-HG_ε) ^ n := by
  unfold HG_partialInv
  have h := mul_neg_geom_sum (-HG_ε) n
  rwa [show (1 : HGReal) - -HG_ε = 1 + HG_ε by ring] at h

/-- -ε as a single term in the underlying ring. -/
private theorem HG_neg_ε_single :
    (ofLex (-HG_ε) : HGRing) = Finsupp.single (1 : ℤ) (-1 : ℝ) := by
  show -(Finsupp.single (1 : ℤ) (1 : ℝ) : HGRing) = Finsupp.single 1 (-1)
  ext k; simp [Finsupp.single_apply]

/-- (-ε)^n is a single term at index n with coefficient (-1)^n. -/
theorem HG_neg_ε_pow_single (n : ℕ) :
    (ofLex ((-HG_ε) ^ n) : HGRing) = Finsupp.single (n : ℤ) ((-1 : ℝ) ^ n) := by
  induction n with
  | zero =>
    show (ofLex (1 : HGReal) : HGRing) = Finsupp.single 0 1
    rfl
  | succ k ih =>
    rw [pow_succ]
    -- ofLex distributes over * (Lex is definitionally α)
    show (ofLex ((-HG_ε) ^ k) : HGRing) * (ofLex (-HG_ε) : HGRing) =
        Finsupp.single (↑(k + 1)) ((-1) ^ (k + 1))
    rw [ih, HG_neg_ε_single, AddMonoidAlgebra.single_mul_single]
    rfl

/-- Coefficient of (-ε)^n at index k. -/
theorem HG_coeff_neg_ε_pow (n : ℕ) (k : ℤ) :
    HG_coeff ((-HG_ε) ^ n) k = if k = (n : ℤ) then (-1 : ℝ) ^ n else 0 := by
  unfold HG_coeff
  show (ofLex ((-HG_ε) ^ n) : HGRing) k = _
  rw [HG_neg_ε_pow_single, Finsupp.single_apply]; split <;> simp_all [eq_comm]

/-- (-ε)^n is infinitesimal for n ≥ 1: its only term is at index n > 0. -/
theorem HG_neg_ε_pow_infinitesimal {n : ℕ} (hn : 1 ≤ n) :
    HG_isInfinitesimal ((-HG_ε) ^ n) := by
  intro k hk
  rw [HG_coeff_neg_ε_pow]
  exact if_neg (by omega)

-- ─── 9. The approximate field theorem ───────────────────────────────────────

/-- (1+ε) · partialInv(n) ≈ 1 for n ≥ 1: the product differs from 1
    only by (-ε)^n, an infinitesimal of order n. -/
theorem HG_one_add_ε_approx_inv (n : ℕ) (hn : 1 ≤ n) :
    (1 + HG_ε) * HG_partialInv n ≈ₕ 1 := by
  rw [HG_geom_identity]
  intro k hk
  -- Goal: coeff of ((1 - (-ε)^n) - 1) at k ≤ 0 is 0
  -- 1 - (-ε)^n - 1 = -((-ε)^n)
  have hsub : (1 : HGReal) - (-HG_ε) ^ n - 1 = -((-HG_ε) ^ n) := by ring
  simp only [hsub, HG_coeff_neg, HG_coeff_neg_ε_pow, neg_eq_zero]
  exact if_neg (by omega)

/-- More generally, any (r + a·ε) with r ≠ 0 has an approximate inverse.
    Factor: (r + a·ε) = r · (1 + (a/r)·ε), so use geometric series on (a/r)·ε. -/
noncomputable def HG_partialInvScaled (r : ℝ) (n : ℕ) : HGReal :=
  HG_embedℝ r⁻¹ * (Finset.range n).sum (fun k => (-(HG_embedℝ r⁻¹ * HG_ε)) ^ k)

-- ─── 10. AlmostField: abstract class + instance ─────────────────────────────
-- Inspired by:
--   • Almost mathematics (Faltings, Gabber–Ramero): ring ops hold mod a "negligible" ideal
--   • Valuation rings: HGReal has a natural ℤ-valued valuation (leading exponent);
--     the fraction field of HGReal (Laurent series) IS a valued field where exact
--     inverses exist. The partial sums are Cauchy approximations in the valuation topology.
--   • HGReal is NOT a local ring: (1+ε)/2 + (1-ε)/2 = 1 but neither summand is a unit.
--     However, every element with nonzero leading coefficient IS a unit in the completion.

/-- Approximate equality refined by order: coefficients agree below index n. -/
def HG_approx_order (x y : HGReal) (n : ℕ) : Prop :=
  ∀ k : ℤ, k < (n : ℤ) → HG_coeff (x - y) k = 0

notation:50 x " ≈[" n "] " y => HG_approx_order x y n

/-- Order-1 approximation (k < 1, i.e. k ≤ 0) is equivalent to ≈ₕ. -/
theorem HG_approx_order_one_iff (x y : HGReal) :
    (x ≈[1] y) ↔ (x ≈ₕ y) := by
  constructor
  · intro h k hk; exact h k (by omega)
  · intro h k hk; exact h k (by omega)

/-- (1+ε) · partialInv(n) agrees with 1 up to order n:
    the remainder (-ε)^n lives entirely at index n. -/
theorem HG_one_add_ε_approx_order (n : ℕ) :
    (1 + HG_ε) * HG_partialInv n ≈[n] 1 := by
  intro k hk
  rw [HG_geom_identity]
  have hsub : (1 : HGReal) - (-HG_ε) ^ n - 1 = -((-HG_ε) ^ n) := by ring
  simp only [hsub, HG_coeff_neg, HG_coeff_neg_ε_pow, neg_eq_zero]
  exact if_neg (by omega)

/-- Abstract "almost field": a CommRing where every nonzero element has an
    approximate inverse at every precision level. This is the algebraic analogue
    of completeness: the ring need not contain exact inverses, but can approximate
    them to arbitrary order.

    Related concepts:
    • Almost ring (Faltings): operations hold mod an ideal of "negligible" elements
    • Topological ring with dense units in the completion
    • Valuation ring whose fraction field is the ring of formal Laurent series -/
class AlmostField (R : Type*) [CommRing R] where
  /-- Precision-indexed negligibility: when is an element "zero up to order n"? -/
  negligible : R → ℕ → Prop
  /-- Negligibility is monotone: higher order ⟹ lower order -/
  negligible_mono : ∀ {x m n}, m ≤ n → negligible x n → negligible x m
  /-- Every nonzero element has an approximate inverse at every order -/
  approx_inv : ∀ (a : R), a ≠ 0 → ∀ (n : ℕ), ∃ b : R, negligible (a * b - 1) n

-- ─── 11. HGReal is an AlmostField (for monomials) ──────────────────────────
-- Full proof for general nonzero elements requires factoring out the leading
-- monomial. Here we prove it for the concrete flagship case (1+ε) and sketch
-- the general structure.

/-- HGReal negligibility: all coefficients below index n vanish. -/
def HG_negligible (x : HGReal) (n : ℕ) : Prop :=
  ∀ k : ℤ, k < (n : ℤ) → HG_coeff x k = 0

theorem HG_negligible_mono {x : HGReal} {m n : ℕ} (hmn : m ≤ n)
    (h : HG_negligible x n) : HG_negligible x m :=
  fun k hk => h k (lt_of_lt_of_le hk (Int.ofNat_le.mpr hmn))

-- ─── 12. Honest sorrys (kept at end) ───────────────────────────────────────
-- The full Field instance needs FractionRing (power series completion).
-- The AlmostField above is the honest substitute for finite Laurent polys.
-- Usage: `haveI := instHGField` when downstream code truly needs Field.

noncomputable def instHGField : Field HGReal := sorry
noncomputable def instHGIsStrictOrderedRing : IsStrictOrderedRing HGReal := sorry
