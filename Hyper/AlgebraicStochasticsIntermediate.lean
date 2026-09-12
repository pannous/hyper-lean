import Hyper.AlgebraicProbability

/-!
  Formal solutions of Exercises 8--14 from
  `notes/counting/algebraic-stochastics-exercises.md`.

  This module deliberately uses `fieldAdd`, `fieldNeg`, `fieldMul`, coefficient-
  wise algebraic equality, and the explicit reciprocal of a proved-nonzero
  monomial count.  It never invokes the backend's inverse on a mixed-order
  expression.

  Exercises 13 and 14 are closed-form algebraic moment identities.  They do
  not claim that the present implementation has a genuine `Fin omega` index
  type; `n` in the collision formulas is an ordinary finite natural number.
-/

namespace Hypers
namespace HyperLists
namespace AlgebraicStochasticsIntermediate

open AlgebraicProbability

private theorem coeffAt_monomial {c : 𝔽} {i order : ℚ} (hc : c ≠ 0) :
    coeffAt (monomial c i) order = if i = order then c else 0 := by
  rw [monomial_of_ne hc, coeffAt_cons, coeffAt_nil]
  simp

private theorem fieldNeg_monomial {c : 𝔽} {i : ℚ} (hc : c ≠ 0) :
    fieldNeg (monomial c i) = monomial (-c) i := by
  rw [monomial_of_ne hc, monomial_of_ne (neg_ne_zero.mpr hc)]
  simp [fieldNeg, normalize, simplify, mergeAdjacent, neg_ne_zero.mpr hc]

private theorem monomial_zero_order_eq_cast {c : 𝔽} (hc : c ≠ 0) :
    monomial c 0 = embedQ c := by
  simp [monomial, hc, embedQ]

private theorem monomial_neg_one_eq_scale {c : 𝔽} (hc : c ≠ 0) :
    monomial c (-1) = fieldMul (embedQ c) epsilon := by
  rw [← monomial_zero_order_eq_cast hc,
    show epsilon = monomial 1 (-1) from monomial_one_neg_one.symm,
    monomial_mul hc one_ne_zero]
  norm_num

private theorem monomial_neg_two_eq_scale_sq {c : 𝔽} (hc : c ≠ 0) :
    monomial c (-2) = fieldMul (embedQ c) (fieldMul epsilon epsilon) := by
  have hepssq : fieldMul epsilon epsilon = monomial 1 (-2) := by
    rw [show epsilon = monomial 1 (-1) from monomial_one_neg_one.symm,
      monomial_mul one_ne_zero one_ne_zero]
    norm_num
  rw [hepssq, ← monomial_zero_order_eq_cast hc, monomial_mul hc one_ne_zero]
  norm_num

/-! ### Exercises 8 and 9: coordinate counts in an omega by omega grid -/

def squareTotal : NonzeroCount := ⟨⟨1, 2⟩, one_ne_zero⟩
def rowCount : Count := ⟨1, 1⟩
def pointCount : Count := ⟨1, 0⟩
def rowProbabilityCount : NonzeroCount := ⟨⟨1, -1⟩, one_ne_zero⟩

def rowProbability : R* := probability rowCount squareTotal
def pointProbability : R* := probability pointCount squareTotal

/-- Exercise 8: after conditioning a specified grid point on its row, its
probability is one among `omega`, namely `epsilon`. -/
theorem point_conditioned_on_row :
    conditional pointProbability rowProbabilityCount = epsilon := by
  unfold conditional pointProbability probability pointCount squareTotal
    rowProbabilityCount NonzeroCount.reciprocalValue
  norm_num only
  rw [monomial_mul one_ne_zero one_ne_zero]
  norm_num

/-- Each coordinate slice has probability `epsilon`. -/
theorem coordinate_slice_probability : rowProbability = epsilon := by
  norm_num [rowProbability, probability, rowCount, squareTotal, monomial,
    epsilon]

/-- A specified point in the product grid has probability `epsilon^2`. -/
theorem coordinate_intersection_probability :
    pointProbability = monomial 1 (-2) := by
  norm_num [pointProbability, probability, pointCount, squareTotal]

/-- Exercise 9: the two coordinate events are independent at the full
infinitesimal resolution, not merely after taking shadows. -/
theorem coordinate_events_independent :
    independentAnd rowProbability rowProbability = pointProbability := by
  rw [coordinate_slice_probability, coordinate_intersection_probability]
  change fieldMul (monomial 1 (-1)) (monomial 1 (-1)) = monomial 1 (-2)
  rw [monomial_mul one_ne_zero one_ne_zero]
  norm_num

/-- Conditioning either coordinate event on the other recovers its original
probability. -/
theorem coordinate_conditioning :
    conditional pointProbability rowProbabilityCount = rowProbability := by
  rw [point_conditioned_on_row, coordinate_slice_probability]

/-! ### Exercise 10: two toroidal diagonals -/

def diagonalProbability : R* := monomial 1 (-1)
def twoDiagonalsProbability : R* := monomial 2 (-1)

/-- A diagonal is not independent of the union of itself with a disjoint
parallel diagonal: `epsilon` is not `epsilon * (2 epsilon)`. -/
theorem diagonal_union_not_independent :
    ¬ (diagonalProbability ≡ₐ
        independentAnd diagonalProbability twoDiagonalsProbability) := by
  intro h
  have hproduct :
      independentAnd diagonalProbability twoDiagonalsProbability =
        monomial 2 (-2) := by
    unfold independentAnd diagonalProbability twoDiagonalsProbability
    rw [monomial_mul one_ne_zero (by norm_num : (2 : 𝔽) ≠ 0)]
    norm_num
  rw [hproduct] at h
  have hAt := h (-1)
  unfold diagonalProbability at hAt
  rw [coeffAt_monomial one_ne_zero,
    coeffAt_monomial (by norm_num : (2 : 𝔽) ≠ 0)] at hAt
  norm_num at hAt

/-- Given that one of two disjoint diagonals occurred, the specified one has
conditional probability exactly one half. -/
theorem diagonal_conditioned_on_union :
    conditional diagonalProbability ⟨⟨2, -1⟩, by norm_num⟩ =
      monomial (1 / 2) 0 := by
  rw [show diagonalProbability = monomial 1 (-1) from rfl]
  unfold conditional NonzeroCount.reciprocalValue
  norm_num only
  rw [monomial_mul one_ne_zero (by norm_num : (1 / 2 : 𝔽) ≠ 0)]
  congr 2
  · rw [div_eq_mul_inv, one_mul]
    change Rat.inv 2 = Rat.inv 2
    rfl
  · norm_num

/-! ### Exercise 11: rare Bernoulli moments -/

def rareChance (c : 𝔽) : R* := monomial c (-1)

def bernoulliSecondMoment (c : 𝔽) : R* :=
  expectation [(zero, complement (rareChance c)), (one, rareChance c)]

def bernoulliVariance (c : 𝔽) : R* :=
  fieldAdd (rareChance c) (fieldNeg (fieldMul (rareChance c) (rareChance c)))

/-- The expectation of the rare Bernoulli variable is `c * epsilon`. -/
theorem rare_bernoulli_expectation (c : 𝔽) :
    expectation [(zero, complement (rareChance c)), (one, rareChance c)]
      ≡ₐ rareChance c :=
  expectation_bernoulli (rareChance c)

/-- Since a Bernoulli variable is idempotent, its second moment is also
`c * epsilon`. -/
theorem rare_bernoulli_second_moment (c : 𝔽) :
    bernoulliSecondMoment c ≡ₐ rareChance c :=
  rare_bernoulli_expectation c

/-- Exact rare-Bernoulli variance, retaining the order-`epsilon^2`
correction: `c epsilon - c^2 epsilon^2`. -/
theorem rare_bernoulli_variance {c : 𝔽} (hc : c ≠ 0) :
    bernoulliVariance c =
      fieldAdd (monomial c (-1)) (fieldNeg (monomial (c ^ 2) (-2))) := by
  unfold bernoulliVariance rareChance
  rw [monomial_mul hc hc]
  congr 4
  · ring
  · norm_num

/-! ### Exercise 12: an infinite payoff on a rare event -/

def rarePayoff (c : 𝔽) : R* := monomial c⁻¹ 1
def rarePayoffMean (c : 𝔽) : R* :=
  fieldMul (rareChance c) (rarePayoff c)
def rarePayoffSecondMoment (c : 𝔽) : R* :=
  fieldMul (rareChance c) (fieldMul (rarePayoff c) (rarePayoff c))
def rarePayoffVariance (c : 𝔽) : R* :=
  fieldAdd (rarePayoffSecondMoment c)
    (fieldNeg (fieldMul (rarePayoffMean c) (rarePayoffMean c)))

/-- The infinitesimal chance and infinite payoff cancel exactly. -/
theorem rare_payoff_mean {c : 𝔽} (hc : c ≠ 0) :
    rarePayoffMean c = one := by
  unfold rarePayoffMean rareChance rarePayoff
  rw [monomial_mul hc (inv_ne_zero hc)]
  rw [show c * c⁻¹ = 1 from mul_inv_cancel₀ hc]
  norm_num

/-- The payoff's second moment is `omega / c`. -/
theorem rare_payoff_second_moment {c : 𝔽} (hc : c ≠ 0) :
    rarePayoffSecondMoment c = monomial c⁻¹ 1 := by
  unfold rarePayoffSecondMoment rareChance rarePayoff
  rw [monomial_mul (inv_ne_zero hc) (inv_ne_zero hc)]
  rw [monomial_mul hc (mul_ne_zero (inv_ne_zero hc) (inv_ne_zero hc))]
  congr 2
  · field_simp
  · norm_num

/-- Its exact variance is `omega / c - 1`, hence it still has an infinite
leading term despite its finite mean. -/
theorem rare_payoff_variance {c : 𝔽} (hc : c ≠ 0) :
    rarePayoffVariance c =
      fieldAdd (monomial c⁻¹ 1) (fieldNeg one) := by
  unfold rarePayoffVariance
  rw [rare_payoff_second_moment hc, rare_payoff_mean hc]
  have hone : fieldMul one one = one := by
    change fieldMul (monomial 1 0) (monomial 1 0) = monomial 1 0
    rw [monomial_mul one_ne_zero one_ne_zero]
    norm_num
  rw [hone]

/-! ### Exercise 13: closed-form uniform-grid moments -/

def oneMinusEpsilon : R* := [(1, 0), (-1, -1)]
def twoMinusEpsilon : R* := [(2, 0), (-1, -1)]

def uniformGridMeanClosed : R* :=
  fieldMul (monomial (1 / 2) 0) oneMinusEpsilon

def uniformGridSecondMomentClosed : R* :=
  fieldMul (monomial (1 / 6) 0)
    (fieldMul oneMinusEpsilon twoMinusEpsilon)

def uniformGridVarianceClosed : R* :=
  fieldAdd uniformGridSecondMomentClosed
    (fieldNeg
      (fieldMul (monomial (1 / 4) 0)
        (fieldMul oneMinusEpsilon oneMinusEpsilon)))

/-- The canonical two-term factor really denotes `1 - epsilon`, at every
Laurent coefficient. -/
theorem one_minus_epsilon_semantics :
    oneMinusEpsilon ≡ₐ fieldAdd one (fieldNeg epsilon) := by
  intro order
  rw [coeffAt_fieldAdd, coeffAt_fieldNeg, coeffAt_one]
  simp [oneMinusEpsilon, epsilon, coeffAt_cons, coeffAt_nil]
  by_cases h0 : order = 0
  · subst order; norm_num
  by_cases h1 : order = -1
  · subst order; norm_num
  simp [h0, Ne.symm h0, Ne.symm h1]

/-- `(omega - 1)/(2 omega) = 1/2 - epsilon/2`, expressed without a
mixed-order division. -/
theorem uniform_grid_mean_correction :
    uniformGridMeanClosed ≡ₐ
      fieldAdd (monomial (1 / 2) 0) (monomial (-1 / 2) (-1)) := by
  intro order
  simp only [uniformGridMeanClosed, coeffAt_mul, coeffAt_fieldAdd]
  simp [oneMinusEpsilon, monomial, coeffAt_cons, coeffAt_nil]
  by_cases h0 : order = 0
  · subst order; norm_num
  by_cases h1 : order = -1
  · subst order; norm_num
  simp [Ne.symm h0, Ne.symm h1]

/-- `((omega-1)(2omega-1))/(6omega^2)` retains both correction orders. -/
theorem uniform_grid_second_moment_correction :
    uniformGridSecondMomentClosed ≡ₐ
      fieldAdd
        (fieldAdd (monomial (1 / 3) 0) (monomial (-1 / 2) (-1)))
        (monomial (1 / 6) (-2)) := by
  intro order
  simp only [uniformGridSecondMomentClosed, coeffAt_mul, coeffAt_fieldAdd]
  simp [oneMinusEpsilon, twoMinusEpsilon, monomial, coeffAt_cons, coeffAt_nil]
  by_cases h0 : order = 0
  · subst order; norm_num
  by_cases h1 : order = -1
  · subst order; norm_num
  by_cases h2 : order = -2
  · subst order; norm_num
  have hshift0 : (0 : ℚ) ≠ order + 1 := by
    intro h
    apply h1
    linarith
  have hshift1 : (-1 : ℚ) ≠ order + 1 := by
    intro h
    apply h2
    linarith
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2,
    hshift0, hshift1]

/-- Subtracting the exact squared mean cancels the order-`epsilon`
correction and leaves `1/12 - epsilon^2/12`. -/
theorem uniform_grid_variance_correction :
    uniformGridVarianceClosed ≡ₐ
      fieldAdd (monomial (1 / 12) 0) (monomial (-1 / 12) (-2)) := by
  intro order
  simp only [uniformGridVarianceClosed, uniformGridSecondMomentClosed,
    coeffAt_fieldAdd, coeffAt_fieldNeg, coeffAt_mul]
  simp [oneMinusEpsilon, twoMinusEpsilon, monomial, coeffAt_cons, coeffAt_nil]
  by_cases h0 : order = 0
  · subst order; norm_num
  by_cases h1 : order = -1
  · subst order; norm_num
  by_cases h2 : order = -2
  · subst order; norm_num
  have hshift0 : (0 : ℚ) ≠ order + 1 := by
    intro h
    apply h1
    linarith
  have hshift1 : (-1 : ℚ) ≠ order + 1 := by
    intro h
    apply h2
    linarith
  simp [Ne.symm h0, Ne.symm h1, Ne.symm h2,
    hshift0, hshift1]

/-! ### Exercise 14: standard-finite collision statistic -/

def pairCount (n : ℕ) : 𝔽 := ((n.choose 2 : ℕ) : 𝔽)

def collisionExpectation (n : ℕ) : R* := monomial (pairCount n) (-1)

def collisionVariance (n : ℕ) : R* :=
  fieldAdd (monomial (pairCount n) (-1))
    (fieldNeg (monomial (pairCount n) (-2)))

/-- Closed-form expectation for an ordinary finite `n`: every one of the
`n.choose 2` unordered-pair indicators has probability `epsilon`. -/
theorem collision_expectation_standard_finite (n : ℕ) :
    collisionExpectation n = monomial (n.choose 2) (-1) := rfl

/-- Closed-form variance for ordinary finite `n`, after the pairwise
covariances have cancelled: `choose(n,2) * epsilon * (1-epsilon)`. -/
theorem collision_variance_standard_finite (n : ℕ) :
    collisionVariance n ≡ₐ
      fieldMul (monomial (pairCount n) (-1))
        oneMinusEpsilon := by
  intro order
  simp only [collisionVariance, coeffAt_fieldAdd, coeffAt_fieldNeg, coeffAt_mul]
  by_cases hpair : pairCount n = 0
  · rw [hpair]
    simp [monomial, oneMinusEpsilon]
    change (0 : 𝔽) =
      (List.map (fun p : 𝔽 × ℚ => p.1 *
        coeffAt [(1, 0), (-1, -1)] (order - p.2)) []).sum
    simp
  · rw [monomial_of_ne hpair]
    simp only [List.map_singleton, List.sum_singleton]
    simp [oneMinusEpsilon, monomial, hpair, coeffAt_cons, coeffAt_nil]
    by_cases h1 : order = -1
    · subst order; norm_num
    by_cases h2 : order = -2
    · subst order; norm_num
    have hshift0 : (0 : ℚ) ≠ order + 1 := by
      intro h
      apply h1
      linarith
    have hshift1 : (-1 : ℚ) ≠ order + 1 := by
      intro h
      apply h2
      linarith
    simp [Ne.symm h1, Ne.symm h2, hshift0, hshift1]

#print axioms point_conditioned_on_row
#print axioms coordinate_events_independent
#print axioms diagonal_union_not_independent
#print axioms diagonal_conditioned_on_union
#print axioms rare_bernoulli_variance
#print axioms rare_payoff_variance
#print axioms uniform_grid_variance_correction
#print axioms collision_variance_standard_finite

end AlgebraicStochasticsIntermediate
end HyperLists
end Hypers
