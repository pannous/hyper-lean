import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Tactic

/-! An exact, purely algebraic ordered field K(ω), with ε = ω⁻¹.
The sign is the sign of the numerator's leading coefficient; Mathlib
normalizes the denominator to be monic. No series, limits, or extra axioms.
Open `scoped AlgebraicHyperreal` to use this ordering on `RatFunc K`. -/

noncomputable section
namespace AlgebraicHyperreal
open Polynomial
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem lc_add_nonneg {p q : K[X]}
    (hp : 0 ≤ p.leadingCoeff) (hq : 0 ≤ q.leadingCoeff) :
    0 ≤ (p + q).leadingCoeff := by
  by_cases hz : p.leadingCoeff + q.leadingCoeff = 0
  · have hp0 : p = 0 := Polynomial.leadingCoeff_eq_zero.mp (by linarith)
    have hq0 : q = 0 := Polynomial.leadingCoeff_eq_zero.mp (by linarith)
    simp [hp0, hq0]
  · rcases lt_trichotomy p.degree q.degree with h | h | h
    · rwa [leadingCoeff_add_of_degree_lt h]
    · rw [leadingCoeff_add_of_degree_eq h hz]
      exact add_nonneg hp hq
    · rwa [leadingCoeff_add_of_degree_lt' h]

theorem num_lc_neg (x : RatFunc K) :
    (-x).num.leadingCoeff = -x.num.leadingCoeff := by
  have h := congrArg Polynomial.leadingCoeff (RatFunc.num_denom_neg x)
  simpa only [leadingCoeff_mul, leadingCoeff_neg,
    (RatFunc.monic_denom _).leadingCoeff, mul_one] using h

theorem num_lc_mul (x y : RatFunc K) :
    (x * y).num.leadingCoeff = x.num.leadingCoeff * y.num.leadingCoeff := by
  have h := congrArg Polynomial.leadingCoeff (RatFunc.num_denom_mul x y)
  simpa only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff,
    mul_one, one_mul] using h

def cone (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    RingCone (RatFunc K) where
  carrier := {x | 0 ≤ x.num.leadingCoeff}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy := by
    have h := congrArg Polynomial.leadingCoeff (RatFunc.num_denom_add x y)
    simp only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff,
      mul_one] at h
    change 0 ≤ (x + y).num.leadingCoeff
    rw [h]
    apply lc_add_nonneg
    · simpa only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff,
        mul_one] using hx
    · simpa only [leadingCoeff_mul, (RatFunc.monic_denom _).leadingCoeff,
        one_mul] using hy
  mul_mem' {x y} hx hy := by
    change 0 ≤ (x * y).num.leadingCoeff
    rw [num_lc_mul]
    exact mul_nonneg hx hy
  eq_zero_of_mem_of_neg_mem' {x} hx hn := by
    change 0 ≤ x.num.leadingCoeff at hx
    change 0 ≤ (-x).num.leadingCoeff at hn
    rw [num_lc_neg] at hn
    apply RatFunc.num_eq_zero_iff.mp
    exact Polynomial.leadingCoeff_eq_zero.mp (by linarith)

instance : HasMemOrNegMem (cone K) where
  mem_or_neg_mem x := by
    change 0 ≤ x.num.leadingCoeff ∨ 0 ≤ (-x).num.leadingCoeff
    rw [num_lc_neg]
    exact le_total 0 x.num.leadingCoeff |>.imp_right neg_nonneg.mpr

scoped instance : LinearOrder (RatFunc K) := by
  classical
  exact .mkOfAddGroupCone (cone K)
open scoped AlgebraicHyperreal
scoped instance : IsOrderedRing (RatFunc K) := .mkOfCone (cone K)

def omega : RatFunc K := RatFunc.X
def epsilon : RatFunc K := (omega (K := K))⁻¹

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem omega_ne_zero : omega (K := K) ≠ 0 := RatFunc.X_ne_zero

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem epsilon_mul_omega : epsilon (K := K) * omega = 1 :=
  inv_mul_cancel₀ omega_ne_zero

theorem nonneg_iff (x : RatFunc K) : 0 ≤ x ↔ 0 ≤ x.num.leadingCoeff := by
  change 0 ≤ (x - 0).num.leadingCoeff ↔ _
  simp

theorem pos_iff (x : RatFunc K) : 0 < x ↔ 0 < x.num.leadingCoeff := by
  rw [lt_iff_le_and_ne, nonneg_iff]
  constructor
  · rintro ⟨h, hn⟩
    exact lt_of_le_of_ne h (fun hz => hn (RatFunc.num_eq_zero_iff.mp
      (Polynomial.leadingCoeff_eq_zero.mp hz.symm)).symm)
  · intro h
    refine ⟨h.le, ?_⟩
    rintro rfl
    simp at h

theorem constant_lt_omega (r : K) : RatFunc.C r < omega (K := K) := by
  rw [← sub_pos, pos_iff]
  have heq : omega (K := K) - RatFunc.C r =
      algebraMap K[X] (RatFunc K) (Polynomial.X - Polynomial.C r) := by
    simp [omega]
  rw [heq, RatFunc.num_algebraMap, (Polynomial.monic_X_sub_C r).leadingCoeff]
  exact zero_lt_one

theorem omega_pos : 0 < omega (K := K) := by simpa using constant_lt_omega (0 : K)

theorem epsilon_pos : 0 < epsilon (K := K) := inv_pos.mpr omega_pos

theorem epsilon_lt_one : epsilon (K := K) < 1 := by
  simpa [epsilon] using inv_lt_one_of_one_lt₀
    (show (1 : RatFunc K) < omega from by simpa using constant_lt_omega (1 : K))

/-- ε is smaller than every positive member of the coefficient field. -/
theorem epsilon_lt_constant {r : K} (hr : 0 < r) :
    epsilon (K := K) < RatFunc.C r := by
  have hc : 0 < RatFunc.C r := by
    rw [pos_iff]
    simpa using hr
  have h := constant_lt_omega (r⁻¹)
  have hi : (RatFunc.C r)⁻¹ < omega (K := K) := by simpa using h
  simpa [epsilon] using (inv_lt_comm₀ omega_pos hc).mpr hi

theorem mixed_inverse :
    (1 + epsilon (K := K)) * (1 + epsilon)⁻¹ = 1 :=
  mul_inv_cancel₀ (ne_of_gt (add_pos zero_lt_one epsilon_pos))

theorem closed_interval_point :
    (omega (K := K) + 1)⁻¹ = epsilon / (1 + epsilon) := by
  have hw := omega_ne_zero (K := K)
  have hwp : omega (K := K) + 1 ≠ 0 := ne_of_gt (add_pos omega_pos zero_lt_one)
  have he : 1 + epsilon (K := K) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  unfold epsilon at *
  field_simp

#print axioms constant_lt_omega
#print axioms epsilon_lt_constant
#print axioms mixed_inverse

end AlgebraicHyperreal
