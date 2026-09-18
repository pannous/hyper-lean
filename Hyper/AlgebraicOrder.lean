import Hyper.CubicContent

/-! Algebraic O-notation: standard-real bounds at a fixed positive gauge.
An O expression specifies a remainder, never a new field element or axiom.
Integer orders include infinite scales. No limits or infinite sums are used.
-/
noncomputable section
open scoped AlgebraicHyperreal
namespace AlgebraicOrder
open AlgebraicHyperreal AlgebraicIntegral GeometricContent
local notation "C" => (RatFunc.C : ℝ →+* H)

theorem constant_abs (a : ℝ) : |C a| = C |a| := by
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg (constant_nonneg ha), abs_of_nonneg ha]
  · have ha' : a < 0 := lt_of_not_ge ha
    have hc : C a < 0 := by
      have h := constant_pos (neg_pos.mpr ha')
      simpa only [map_neg, neg_pos] using h
    rw [abs_of_neg hc, abs_of_neg ha', map_neg]

def IsO (g : H) (n : ℤ) (x : H) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ |x| ≤ C M * g ^ n

/-- Read as x = y + O(g^n), not as exact equality of field elements. -/
def Approx (g : H) (n : ℤ) (x y : H) : Prop := IsO g n (x - y)

namespace IsO
variable {g x y : H} {m n : ℤ}

theorem zero (g : H) (n : ℤ) : IsO g n 0 := by
  exact ⟨0, le_refl _, by simp⟩

theorem monomial (hg : 0 < g) (a : ℝ) (n : ℤ) : IsO g n (C a * g ^ n) := by
  refine ⟨|a|, abs_nonneg _, ?_⟩
  rw [abs_mul, abs_of_pos (zpow_pos hg n), constant_abs]

theorem neg (hx : IsO g n x) : IsO g n (-x) := by
  simpa only [IsO, abs_neg] using hx

theorem add (hx : IsO g n x) (hy : IsO g n y) : IsO g n (x + y) := by
  obtain ⟨A, hA, hx⟩ := hx
  obtain ⟨B, hB, hy⟩ := hy
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  calc
    |x + y| ≤ |x| + |y| := abs_add_le _ _
    _ ≤ C A * g ^ n + C B * g ^ n := add_le_add hx hy
    _ = C (A + B) * g ^ n := by rw [map_add, add_mul]

theorem sub (hx : IsO g n x) (hy : IsO g n y) : IsO g n (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem mul (hg : 0 < g) (hx : IsO g m x) (hy : IsO g n y) :
    IsO g (m + n) (x * y) := by
  obtain ⟨A, hA, hx⟩ := hx
  obtain ⟨B, hB, hy⟩ := hy
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  rw [abs_mul]
  calc
    |x| * |y| ≤ (C A * g ^ m) * (C B * g ^ n) :=
      mul_le_mul hx hy (abs_nonneg _) (mul_nonneg (constant_nonneg hA) (zpow_pos hg m).le)
    _ = C (A * B) * g ^ (m + n) := by rw [map_mul, zpow_add₀ (ne_of_gt hg)]; ring

theorem weaken (hg : 0 < g) (hg1 : g ≤ 1) (hx : IsO g n x) (hmn : m ≤ n) :
    IsO g m x := by
  obtain ⟨A, hA, hx⟩ := hx
  exact ⟨A, hA, hx.trans (mul_le_mul_of_nonneg_left
    (zpow_le_zpow_right_of_le_one₀ hg hg1 hmn) (constant_nonneg hA))⟩

theorem div_gauge (hg : 0 < g) (hx : IsO g n x) (m : ℤ) :
    IsO g (n - m) (x / g ^ m) := by
  have hm := monomial hg 1 (-m)
  simp only [map_one, one_mul, zpow_neg] at hm
  simpa only [sub_eq_add_neg, div_eq_mul_inv] using hx.mul hg hm

end IsO

theorem isO_iff_scaled {g x : H} (hg : 0 < g) (n : ℤ) :
    IsO g n x ↔ IsO g 0 (x / g ^ n) := by
  constructor
  · intro h
    simpa only [sub_self] using h.div_gauge hg n
  · intro h
    have hm := h.mul hg (IsO.monomial hg 1 n)
    simpa only [zero_add, map_one, one_mul,
      div_mul_cancel₀ _ (zpow_ne_zero n (ne_of_gt hg))] using hm

/-- The standard-real bound is essential: allowing arbitrary hyperreal
constants would make every O class the whole field. -/
theorem one_not_isO_epsilon : ¬ IsO (epsilon (K := ℝ)) 1 1 := by
  rintro ⟨M, hM, h⟩
  simp only [abs_one, zpow_one] at h
  by_cases hz : M = 0
  · rw [hz, map_zero, zero_mul] at h
    exact not_le_of_gt zero_lt_one h
  · have hp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
    have hc := constant_pos hp
    have he := epsilon_lt_constant (inv_pos.mpr hp)
    rw [map_inv₀] at he
    have hh := mul_lt_mul_of_pos_left he hc
    rw [mul_inv_cancel₀ (ne_of_gt hc)] at hh
    exact (not_lt_of_ge h) hh

namespace Approx
variable {g x y z u v : H} {n : ℤ}

theorem refl (g : H) (n : ℤ) (x : H) : Approx g n x x := by
  simpa [Approx] using IsO.zero g n

theorem symm (h : Approx g n x y) : Approx g n y x := by
  simpa only [Approx, neg_sub] using h.neg

theorem trans (hxy : Approx g n x y) (hyz : Approx g n y z) : Approx g n x z := by
  have h := hxy.add hyz
  simpa only [sub_add_sub_cancel] using h

theorem add (hxy : Approx g n x y) (huv : Approx g n u v) :
    Approx g n (x + u) (y + v) := by
  have h := IsO.add hxy huv
  have heq : (x + u) - (y + v) = (x - y) + (u - v) := by ring
  unfold Approx
  rw [heq]
  exact h

/-- Multiplication preserves an absolute error order when these factors
are bounded by standard reals. General orders use IsO.mul instead. -/
theorem mul (hg : 0 < g) (hxy : Approx g n x y) (huv : Approx g n u v)
    (hu : IsO g 0 u) (hy : IsO g 0 y) : Approx g n (x * u) (y * v) := by
  have h₁ := IsO.mul hg hxy hu
  have h₂ := IsO.mul hg hy huv
  simp only [add_zero, zero_add] at h₁ h₂
  have h := h₁.add h₂
  have heq : x * u - y * v = (x - y) * u + y * (u - v) := by ring
  unfold Approx
  rw [heq]
  exact h

/-- Reciprocal errors keep their order only with controlled reciprocals.
For infinitesimal denominators, use explicit scale tracking instead. -/
theorem inv (hg : 0 < g) (hxy : Approx g n x y) (hx : x ≠ 0) (hy : y ≠ 0)
    (hix : IsO g 0 x⁻¹) (hiy : IsO g 0 y⁻¹) : Approx g n x⁻¹ y⁻¹ := by
  have h := (IsO.mul hg (IsO.mul hg hxy hix) hiy).neg
  simp only [add_zero] at h
  have heq : x⁻¹ - y⁻¹ = -((x - y) * x⁻¹ * y⁻¹) := by field_simp; ring
  unfold Approx
  rw [heq]
  exact h

theorem div_gauge (hg : 0 < g) (hxy : Approx g n x y) (m : ℤ) :
    Approx g (n - m) (x / g ^ m) (y / g ^ m) := by
  unfold Approx
  rw [← sub_div]
  exact IsO.div_gauge hg hxy m

theorem weaken (hg : 0 < g) (hg1 : g ≤ 1) (hxy : Approx g n x y)
    (m : ℤ) (hmn : m ≤ n) : Approx g m x y :=
  IsO.weaken hg hg1 hxy hmn

end Approx

/-- A useful algebraic reciprocal expansion with an explicitly bounded tail. -/
theorem inverse_one_add (g : H) (hg : 0 < g) :
    Approx g 2 (1 + g)⁻¹ (1 - g) := by
  have hne : 1 + g ≠ 0 := ne_of_gt (add_pos zero_lt_one hg)
  have hi : IsO g 0 (1 + g)⁻¹ := by
    refine ⟨1, zero_le_one, ?_⟩
    simp only [map_one, zpow_zero, mul_one, abs_of_pos (inv_pos.mpr
      (add_pos zero_lt_one hg))]
    exact (inv_le_one₀ (add_pos zero_lt_one hg)).mpr (by linarith)
  have h := IsO.mul hg (IsO.monomial hg 1 2) hi
  simp only [map_one, one_mul, add_zero, zpow_ofNat] at h
  have heq : (1 + g)⁻¹ - (1 - g) = g ^ 2 * (1 + g)⁻¹ := by field_simp; ring
  unfold Approx
  rw [heq]
  exact h

/-- A uniform remainder bound survives any positive normalized integral.
The same M must bound every observable region. -/
theorem integral_isO_of_uniform_bound {ι : Type*} [Fintype ι]
    (Ω : Context H ι) (g : H) (n : ℤ) (f : ι → H)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ i, |f i| ≤ C M * g ^ n) :
    IsO g n (Ω.integral f) := by
  refine ⟨M, hM, abs_le.mpr ⟨?_, ?_⟩⟩
  · have h := Ω.integral_mono (fun i => (abs_le.mp (hf i)).1)
    simpa only [Context.integral_const] using h
  · have h := Ω.integral_mono (fun i => (abs_le.mp (hf i)).2)
    simpa only [Context.integral_const] using h

theorem integral_approx_of_uniform_bound {ι : Type*} [Fintype ι]
    (Ω : Context H ι) (g : H) (n : ℤ) (f h : ι → H)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ i, |f i - h i| ≤ C M * g ^ n) :
    Approx g n (Ω.integral f) (Ω.integral h) := by
  have ho := integral_isO_of_uniform_bound Ω g n (fun i => f i - h i) M hM hf
  have heq : Ω.integral f - Ω.integral h = Ω.integral (fun i => f i - h i) := by
    simp only [Context.integral, Context.raw, sub_mul, Finset.sum_sub_distrib, sub_div]
  unfold Approx
  rw [heq]
  exact ho

/-- Every normalized planar closed segment admits the displayed precision. -/
theorem planar_segment (L : ℝ) :
    Approx effectiveEpsilon 2 (GeometricContent.probability (closedSegment L))
      (C L * effectiveEpsilon) := by
  unfold Approx
  rw [segment_probability_effective, add_sub_cancel_left]
  simpa only [map_sub, map_one, zpow_ofNat] using
    IsO.monomial effective_epsilon_pos (1 - L) 2

theorem spatial_segment (L : ℝ) :
    Approx effectiveEpsilon 3 (CubicContent.probability (CubicContent.segment L))
      (C L * effectiveEpsilon ^ 2) := by
  unfold Approx
  rw [CubicContent.segment_probability, add_sub_cancel_left]
  simpa only [map_sub, map_one, zpow_ofNat] using
    IsO.monomial effective_epsilon_pos (1 - L) 3

theorem spatial_surface (A P : ℝ) :
    Approx effectiveEpsilon 2 (CubicContent.probability (CubicContent.surface A P))
      (C A * effectiveEpsilon) := by
  have h₂ := IsO.monomial effective_epsilon_pos (P / 2 - 2 * A) 2
  have h₃ := IsO.monomial effective_epsilon_pos (A - P / 2 + 1) 3
  have hg1 : effectiveEpsilon ≤ 1 :=
    (effective_epsilon_lt_epsilon.trans (epsilon_lt_one (K := ℝ))).le
  have h := h₂.add (h₃.weaken effective_epsilon_pos hg1 (show (2 : ℤ) ≤ 3 by norm_num))
  unfold Approx
  rw [CubicContent.surface_probability]
  convert h using 1
  simp only [map_add, map_sub, map_mul, map_ofNat, map_one, zpow_ofNat]
  ring

/-- Cancelling displayed leading terms does not prove that the result is zero. -/
theorem cancellation_retains_remainder :
    (1 + effectiveEpsilon) - 1 = effectiveEpsilon ∧ effectiveEpsilon ≠ 0 := by
  exact ⟨by ring, ne_of_gt effective_epsilon_pos⟩

end AlgebraicOrder
