import Hyper.AlgebraicTransfer

/-! Using the transfer principle and algebraic roots:
prove a fact over ℝ once, get it for the hyperreals. -/

noncomputable section
namespace AlgebraicTransfer.Examples
open AlgebraicTransfer HyperAlgebraic Formula Term

theorem epsilon_pos : 0 < epsilon := by
  simpa [epsilon] using ofBase_lt_ofBase (AlgebraicHyperreal.epsilon_pos (K := ℝ))

theorem epsilon_lt_one : epsilon < 1 := by
  simpa [epsilon] using ofBase_lt_ofBase (AlgebraicHyperreal.epsilon_lt_one (K := ℝ))

theorem epsilon_inv : epsilon⁻¹ = omega := by
  simp [epsilon, omega, AlgebraicHyperreal.epsilon, map_inv₀]

theorem epsilon_mul_omega : epsilon * omega = 1 := by
  rw [← epsilon_inv, mul_inv_cancel₀ epsilon_pos.ne']

/-- `0 < x → ¬(x + x⁻¹ < 2)` -/
def sumWithInverseAtLeastTwo : Formula 1 :=
  imp (lt (const 0) (var 0)) (.not (lt (add (var 0) (inv (var 0))) (const 2)))

theorem sumWithInverseAtLeastTwo_real (v : Fin 1 → ℝ) : sumWithInverseAtLeastTwo.HoldsReal v := by
  simp only [sumWithInverseAtLeastTwo, imp, HoldsReal, Holds, Term.eval, id, not_lt]
  by_cases hx : 0 < v 0
  · right
    have := mul_inv_cancel₀ hx.ne'
    nlinarith [sq_nonneg (v 0 - 1), inv_pos.mpr hx]
  · left; exact not_lt.mp hx

/-- ε + ω ≥ 2, by transfer from the real AM-GM instance, no hyperreal algebra needed. -/
theorem epsilon_add_omega_ge_two : ¬(epsilon + omega < ofReal 2) := by
  have h := transfer sumWithInverseAtLeastTwo sumWithInverseAtLeastTwo_real ![epsilon]
  simp only [sumWithInverseAtLeastTwo, imp, HoldsHyper, Holds, Term.eval,
    Matrix.cons_val_fin_one, ofReal, map_zero, epsilon_inv] at h
  exact h.resolve_left (not_not.mpr epsilon_pos)

/-- `0 < x < y → y⁻¹ < x⁻¹` -/
def inverseAntitone : Formula 2 :=
  imp (.and (lt (const 0) (var 0)) (lt (var 0) (var 1))) (lt (inv (var 1)) (inv (var 0)))

theorem inverseAntitone_real (v : Fin 2 → ℝ) : inverseAntitone.HoldsReal v := by
  simp only [inverseAntitone, imp, HoldsReal, Holds, Term.eval, id, not_and_or, not_lt]
  by_cases h0 : 0 < v 0
  · by_cases h1 : v 0 < v 1
    · exact Or.inr (inv_strictAnti₀ h0 h1)
    · exact Or.inl (Or.inr (not_lt.mp h1))
  · exact Or.inl (Or.inl (not_lt.mp h0))

/-- ε < 1 transfers to 1 < ω. -/
theorem one_lt_omega_by_transfer : 1 < omega := by
  have h := transfer inverseAntitone inverseAntitone_real ![epsilon, 1]
  simp only [inverseAntitone, imp, HoldsHyper, Holds, Term.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, ofReal, map_zero, epsilon_inv, inv_one] at h
  exact h.resolve_left (not_not.mpr ⟨epsilon_pos, epsilon_lt_one⟩)

/-! ### Roots, symbolically: `√x` is the germ `s ↦ √x(s)`, no series -/

theorem omega_nonneg : 0 ≤ omega := zero_le_one.trans one_lt_omega_by_transfer.le

theorem sqrt_omega_squared : HyperAlgebraic.sqrt omega * HyperAlgebraic.sqrt omega = omega := sqrt_mul_self omega_nonneg

theorem sqrt_one_add_omega_squared :
    HyperAlgebraic.sqrt (1 + omega) * HyperAlgebraic.sqrt (1 + omega) = 1 + omega :=
  sqrt_mul_self (add_nonneg zero_le_one omega_nonneg)

theorem cube_root_of_minus_omega : ∃ y : Number, y ^ 3 = -omega :=
  exists_pow_eq_of_odd (by decide) (-omega)

theorem fifth_root_of_epsilon : ∃ y : Number, 0 ≤ y ∧ y ^ 5 = epsilon :=
  exists_pow_eq_of_nonneg (by decide) epsilon_pos.le

/-- `x ≥ 0 ∧ y ≥ 0 → √(x·y) = √x · √y`, with `√` as a transferred function symbol. -/
def sqrtMultiplicative : Formula 2 :=
  imp (.and (.not (lt (var 0) (const 0))) (.not (lt (var 1) (const 0))))
    (eq (sqrt (mul (var 0) (var 1))) (mul (sqrt (var 0)) (sqrt (var 1))))

theorem sqrtMultiplicative_real (v : Fin 2 → ℝ) : sqrtMultiplicative.HoldsReal v := by
  simp only [sqrtMultiplicative, imp, HoldsReal, Holds, Term.eval, id, not_lt, not_and_or]
  by_cases h0 : 0 ≤ v 0
  · exact Or.inr (Real.sqrt_mul h0 _)
  · exact Or.inl (Or.inl h0)

/-- `√1 = 1` -/
def sqrtOne : Formula 0 := eq (sqrt (const 1)) (const 1)

/-- √ε · √ω = 1, purely by transfer of two real facts. -/
theorem sqrt_epsilon_mul_sqrt_omega :
    HyperAlgebraic.sqrt epsilon * HyperAlgebraic.sqrt omega = 1 := by
  have hmul := transfer sqrtMultiplicative sqrtMultiplicative_real ![epsilon, omega]
  have hone := transfer sqrtOne (fun _ => Real.sqrt_one) ![]
  simp only [sqrtMultiplicative, imp, HoldsHyper, Holds, Term.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, ofReal, map_zero, epsilon_mul_omega, not_lt] at hmul
  simp only [sqrtOne, HoldsHyper, Holds, Term.eval, ofReal, map_one] at hone
  rw [← hmul.resolve_left (not_not.mpr ⟨epsilon_pos.le, omega_nonneg⟩), hone]

#print axioms transfer
#print axioms epsilon_add_omega_ge_two
#print axioms sqrt_epsilon_mul_sqrt_omega
#print axioms cube_root_of_minus_omega

end AlgebraicTransfer.Examples
