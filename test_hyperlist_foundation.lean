import Hyper.HyperListProbability
import Hyper.HyperListSemantics

/-! The legacy bridge is isolated from test_algebraic.lean.
All dependencies printed here are checked against an explicit axiom allowlist. -/
noncomputable section
open HyperListFoundation
open scoped AlgebraicHyperreal

/-- The old representation really does distinguish duplicate lists structurally. -/
theorem raw_lists_differ :
    ([(1, -1), (1, -1)] : Hypers.HyperList) ≠ [(2, -1)] := by decide

/-- The sound semantics identifies their values without equating the lists. -/
theorem duplicate_lists_same_value :
    HyperListSemantics.exactValue [(1, -1), (1, -1)] =
      HyperListSemantics.exactValue [(2, -1)] := by
  apply (HyperListSemantics.exactValue_eq_iff _ _).mpr
  intro e
  simp only [Hypers.coeffAt_cons, Hypers.coeffAt_nil]
  split_ifs <;> norm_num

/-- Full rational exponents are supported by the legacy semantic bridge. -/
theorem rational_orders_multiply :
    HyperListSemantics.exactValue (Hypers.fieldMul [(1, -1/2)] [(1, -1/2)]) =
      HyperListSemantics.exactValue [(1, -1)] := by
  apply (HyperListSemantics.exactValue_eq_iff _ _).mpr
  intro e
  rw [Hypers.coeffAt_mul]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Hypers.coeffAt_cons, Hypers.coeffAt_nil]
  by_cases h : (-1 : ℚ) = e
  · subst e
    norm_num
  · have h' : (-1/2 : ℚ) ≠ e - (-1/2) := by intro hc; apply h; linarith
    simp [h, h']

/-- Reciprocating each monomial in a mixed sum is not a field inverse. -/
theorem termwise_reciprocal_fails :
    eval (mul ([(1, 0), (1, -1)] : Terms ℝ) [(1, 0), (1, 1)]) ≠ 1 := by
  rw [eval_mul]
  simp only [HyperListFoundation.eval, map_one, zpow_zero, zpow_neg_one, zpow_one, one_mul, add_zero]
  have hw : (0 : RatFunc ℝ) < RatFunc.X := AlgebraicHyperreal.omega_pos
  have he : (0 : RatFunc ℝ) < (RatFunc.X : RatFunc ℝ)⁻¹ := inv_pos.mpr hw
  have h : 1 < (1 + (RatFunc.X : RatFunc ℝ)⁻¹) * (1 + RatFunc.X) := by
    nlinarith [mul_pos he hw]
  exact ne_of_gt h

/-- A disk point's exact probability is a fraction of two sparse lists. -/
def diskPointLists : Fraction ℝ where
  numerator := [(1, -2)]
  denominator := diskTerms
  denominator_ne_zero := by
    rw [eval_diskTerms]
    exact ne_of_gt RoundContent.unit_disk_pos

theorem disk_point_lists_value : diskPointLists.value =
    RoundContent.diskProbability (AlgebraicHyperreal.epsilon ^ 2) := by
  simp [diskPointLists, Fraction.value, RoundContent.diskProbability,
    AlgebraicHyperreal.epsilon, AlgebraicHyperreal.omega, zpow_neg, inv_pow]
  rfl

#print axioms HyperListFoundation.eval_add
#print axioms HyperListFoundation.eval_neg
#print axioms HyperListFoundation.eval_mul
#print axioms HyperListFoundation.eval_ofPolynomial
#print axioms HyperListFoundation.Fraction.value_surjective
#print axioms HyperListFoundation.Fraction.value_plus
#print axioms HyperListFoundation.Fraction.value_times
#print axioms HyperListFoundation.Fraction.value_reciprocal
#print axioms HyperListFoundation.Fraction.value_eq_iff_cross_multiply
#print axioms HyperListFoundation.exactEquiv
#print axioms HyperListFoundation.instFieldExact
#print axioms HyperListFoundation.exact_plus
#print axioms HyperListFoundation.exact_times
#print axioms HyperListFoundation.Fraction.value_contextIntegral
#print axioms HyperListFoundation.Fraction.contextIntegral_one
#print axioms HyperListFoundation.eval_epsilonTerms
#print axioms HyperListFoundation.eval_intervalTerms
#print axioms HyperListFoundation.eval_diskTerms
#print axioms HyperListFoundation.eval_ballTerms
#print axioms HyperListFoundation.calibratedPoint_value
#print axioms HyperListFoundation.squareTerms_value
#print axioms HyperListFoundation.cubeTerms_value
#print axioms HyperListSemantics.interpret_eq_iff
#print axioms HyperListSemantics.interpret_simplify
#print axioms HyperListSemantics.interpret_add
#print axioms HyperListSemantics.interpret_neg
#print axioms HyperListSemantics.interpret_mul
#print axioms HyperListSemantics.exactValue_eq_iff
#print axioms HyperListSemantics.exactValue_mul
#print axioms raw_lists_differ
#print axioms duplicate_lists_same_value
#print axioms rational_orders_multiply
#print axioms termwise_reciprocal_fails
#print axioms disk_point_lists_value
