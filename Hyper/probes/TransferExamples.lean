import Hyper.AlgebraicTransfer

/-! Using the transfer principle: prove a fact over ℝ once, get it in ℝ(ω). -/

noncomputable section
namespace AlgebraicTransfer.Examples
open AlgebraicTransfer AlgebraicHyperreal Formula Term
open scoped AlgebraicHyperreal

/-- `0 < x → ¬(x + x⁻¹ < 2)` -/
def sumWithInverseAtLeastTwo : Formula 1 :=
  imp (lt (const 0) (var 0)) (.not (lt (add (var 0) (inv (var 0))) (const 2)))

theorem sumWithInverseAtLeastTwo_real (v : Fin 1 → ℝ) :
    sumWithInverseAtLeastTwo.Holds id v := by
  simp only [sumWithInverseAtLeastTwo, imp, Holds, Term.eval, id, not_lt]
  by_cases hx : 0 < v 0
  · right
    have := mul_inv_cancel₀ hx.ne'
    nlinarith [sq_nonneg (v 0 - 1), inv_pos.mpr hx]
  · left; exact not_lt.mp hx

/-- ε + ω ≥ 2, by transfer from the real AM-GM instance, no hyperreal algebra needed. -/
theorem epsilon_add_omega_ge_two : ¬(epsilon (K := ℝ) + omega < RatFunc.C 2) := by
  have h := transfer sumWithInverseAtLeastTwo sumWithInverseAtLeastTwo_real ![epsilon]
  simp only [sumWithInverseAtLeastTwo, imp, Holds, Term.eval, Matrix.cons_val_fin_one,
    map_zero] at h
  have hinv : (epsilon (K := ℝ))⁻¹ = omega := by simp [epsilon]
  rw [hinv] at h
  exact h.resolve_left (not_not.mpr epsilon_pos)

/-- `0 < x < y → y⁻¹ < x⁻¹` -/
def inverseAntitone : Formula 2 :=
  imp (.and (lt (const 0) (var 0)) (lt (var 0) (var 1))) (lt (inv (var 1)) (inv (var 0)))

theorem inverseAntitone_real (v : Fin 2 → ℝ) : inverseAntitone.Holds id v := by
  simp only [inverseAntitone, imp, Holds, Term.eval, id, not_and_or, not_lt]
  by_cases h0 : 0 < v 0
  · by_cases h1 : v 0 < v 1
    · exact Or.inr (inv_strictAnti₀ h0 h1)
    · exact Or.inl (Or.inr (not_lt.mp h1))
  · exact Or.inl (Or.inl (not_lt.mp h0))

/-- ε < 1 transfers to 1 < ω. -/
theorem one_lt_omega_by_transfer : (1 : Hyperreal) < omega := by
  have h := transfer inverseAntitone inverseAntitone_real ![epsilon, 1]
  simp only [inverseAntitone, imp, Holds, Term.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, map_zero] at h
  have hinv : (epsilon (K := ℝ))⁻¹ = omega := by simp [epsilon]
  rw [hinv, inv_one] at h
  exact h.resolve_left (not_not.mpr ⟨epsilon_pos, epsilon_lt_one⟩)

#print axioms transfer
#print axioms epsilon_add_omega_ge_two
#print axioms one_lt_omega_by_transfer
#print axioms no_sqrt_omega

end AlgebraicTransfer.Examples
