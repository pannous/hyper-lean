/-
  Worked algebraic stochastics exercises 1--7.

  These are direct count-ratio theorems. The ambient
  one-dimensional experiment has algebraic count `omega`; the square has
  count `omega^2`.  Every division below is by one proved-nonzero monomial,
  the exact fragment supported by `AlgebraicProbability`.
-/
import Hyper.AlgebraicProbability

namespace Hypers
namespace HyperLists
namespace AlgebraicStochasticsBasic

open AlgebraicProbability

/-- The one-dimensional uniform experiment has `omega` outcomes. -/
def omegaTotal : NonzeroCount :=
  ⟨⟨1, 1⟩, one_ne_zero⟩

/-- The two-dimensional uniform grid has `omega^2` outcomes. -/
def omegaSquareTotal : NonzeroCount :=
  ⟨⟨1, 2⟩, one_ne_zero⟩

/-- Probability of a standard finite count of favorable outcomes among
`omega` outcomes. -/
def finiteProbability (r : 𝔽) : R* :=
  probability ⟨r, 0⟩ omegaTotal

/-- Coefficients of a canonical monomial, including the zero-coefficient
case.  This is useful when a count identity can cancel to zero. -/
theorem coeffAt_monomial (c : 𝔽) (e order : ℚ) :
    coeffAt (monomial c e) order = if e = order then c else 0 := by
  by_cases hc : c = 0
  · subst c
    rw [monomial_zero]
    change coeffAt ([] : R*) order = (if e = order then 0 else 0)
    simp [coeffAt_nil]
  · rw [monomial_of_ne hc, coeffAt_cons, coeffAt_nil]
    simp

theorem finiteProbability_eq_monomial (r : 𝔽) :
    finiteProbability r = monomial r (-1) := by
  unfold finiteProbability probability omegaTotal
  norm_num

/-! ## Exercise 1 -- one exact outcome -/

/-- Exercise 1: one specified outcome among `omega` has probability
exactly `epsilon`. -/
theorem exercise1_singleton_probability :
    finiteProbability 1 = ε := by
  rw [finiteProbability_eq_monomial, monomial_one_neg_one]

/-- Exercise 1: the singleton remains algebraically possible. -/
theorem exercise1_singleton_positive :
    (0 : R*) < finiteProbability 1 := by
  rw [exercise1_singleton_probability]
  exact epsilon_pos

/-- Exercise 1: taking the ordinary standard coefficient discards the
positive infinitesimal. -/
theorem exercise1_singleton_standard_part :
    st (finiteProbability 1) = 0 := by
  rw [exercise1_singleton_probability]
  exact standard_epsilon_zero

/-! ## Exercise 2 -- a finite target -/

/-- Exercise 2: `r` specified outcomes have probability `r * epsilon`,
represented canonically as the order `-1` monomial. -/
theorem exercise2_finite_target_probability (r : 𝔽) :
    finiteProbability r = monomial r (-1) :=
  finiteProbability_eq_monomial r

/-- The exact reciprocal used to divide by the singleton probability. -/
def singletonProbabilityCount : NonzeroCount :=
  ⟨⟨1, -1⟩, one_ne_zero⟩

/-- Exercise 2: before taking standard parts, the likelihood ratio of an
`r`-outcome target to a singleton is exactly the standard coefficient `r`. -/
theorem exercise2_target_singleton_ratio {r : 𝔽} (hr : r ≠ 0) :
    conditional (finiteProbability r) singletonProbabilityCount =
      monomial r 0 := by
  rw [finiteProbability_eq_monomial]
  unfold conditional singletonProbabilityCount NonzeroCount.reciprocalValue
  change fieldMul (monomial r (-1)) (monomial (1 : 𝔽)⁻¹ (-(-1 : ℚ))) =
    monomial r 0
  norm_num only [inv_one, neg_neg]
  rw [monomial_mul hr one_ne_zero]
  norm_num

/-! ## Exercise 3 -- finite inclusion-exclusion -/

/-- Exercise 3: the count `a + b - c` gives the union probability. -/
theorem exercise3_union_probability_from_count (a b c : 𝔽) :
    finiteProbability (a + b - c) = monomial (a + b - c) (-1) :=
  finiteProbability_eq_monomial _

/-- Exercise 3: inclusion-exclusion holds at every algebraic coefficient,
even when raw HyperList ordering is not a safe notion of equality. -/
theorem exercise3_inclusion_exclusion (a b c : 𝔽) :
    finiteProbability (a + b - c) ≡ₐ
      fieldAdd
        (fieldAdd (finiteProbability a) (finiteProbability b))
        (fieldNeg (finiteProbability c)) := by
  intro order
  rw [finiteProbability_eq_monomial, finiteProbability_eq_monomial,
    finiteProbability_eq_monomial, finiteProbability_eq_monomial]
  rw [coeffAt_fieldAdd, coeffAt_fieldAdd, coeffAt_fieldNeg]
  repeat' rw [coeffAt_monomial]
  by_cases h : (-1 : ℚ) = order <;> simp [h]
  ring

/-- Exercise 3, disjoint specialization: the overlap coefficient is zero. -/
theorem exercise3_disjoint_union (a b : 𝔽) :
    finiteProbability (a + b) ≡ₐ
      fieldAdd (finiteProbability a) (finiteProbability b) := by
  intro order
  rw [finiteProbability_eq_monomial, finiteProbability_eq_monomial,
    finiteProbability_eq_monomial, coeffAt_fieldAdd]
  repeat' rw [coeffAt_monomial]
  by_cases h : (-1 : ℚ) = order <;> simp [h]

/-! ## Exercise 4 -- the dart: point versus segment -/

/-- Probability of `c * omega^d` favorable grid sites among `omega^2`. -/
def squareProbability (c : 𝔽) (d : ℚ) : R* :=
  probability ⟨c, d⟩ omegaSquareTotal

theorem squareProbability_eq_monomial (c : 𝔽) (d : ℚ) :
    squareProbability c d = monomial c (d - 2) := by
  unfold squareProbability probability omegaSquareTotal
  norm_num

/-- Exercise 4: a specified grid point has probability `epsilon^2`. -/
theorem exercise4_point_probability :
    squareProbability 1 0 = monomial 1 (-2) := by
  rw [squareProbability_eq_monomial]
  norm_num

/-- Exercise 4: a segment with `L * omega` grid sites has probability
`L * epsilon`. -/
theorem exercise4_segment_probability (L : 𝔽) :
    squareProbability L 1 = monomial L (-1) := by
  rw [squareProbability_eq_monomial]
  norm_num

/-- The point probability is a proved-nonzero monomial denominator. -/
def pointProbabilityCount : NonzeroCount :=
  ⟨⟨1, -2⟩, one_ne_zero⟩

/-- Exercise 4: `(L * epsilon) / epsilon^2 = L * omega` exactly. -/
theorem exercise4_segment_point_ratio {L : 𝔽} (hL : L ≠ 0) :
    conditional (squareProbability L 1) pointProbabilityCount =
      monomial L 1 := by
  rw [exercise4_segment_probability]
  unfold conditional pointProbabilityCount NonzeroCount.reciprocalValue
  change fieldMul (monomial L (-1)) (monomial (1 : 𝔽)⁻¹ (-(-2 : ℚ))) =
    monomial L 1
  norm_num only [inv_one, neg_neg]
  rw [monomial_mul hL one_ne_zero]
  norm_num

/-! ## Exercise 5 -- coefficients cannot defeat rarity order -/

/-- Exercise 5: `M` specified points have the order `-2` probability. -/
theorem exercise5_many_points_probability (M : 𝔽) :
    squareProbability M 0 = monomial M (-2) := by
  rw [squareProbability_eq_monomial]
  norm_num

/-- Exercise 5: one complete row has probability `epsilon`. -/
theorem exercise5_row_probability :
    squareProbability 1 1 = ε := by
  rw [exercise4_segment_probability, monomial_one_neg_one]

/-- Exercise 5: the disjoint union visibly retains both rarity orders. -/
theorem exercise5_disjoint_union (M : 𝔽) :
    fieldAdd (squareProbability 1 1) (squareProbability M 0) ≡ₐ
      fieldAdd ε (monomial M (-2)) := by
  rw [exercise5_row_probability, exercise5_many_points_probability]
  exact fun _ => rfl

/-- Exercise 5: no positive standard coefficient `M` can promote finitely
many points above one complete row. -/
theorem exercise5_rarity_dominance {M : 𝔽} (hM : 0 < M) :
    squareProbability M 0 < squareProbability 1 1 := by
  have hpoints : squareProbability M 0 = ([(M, -2)] : R*) := by
    rw [exercise5_many_points_probability, monomial_of_ne hM.ne']
  have hrow : squareProbability 1 1 = ([(1, -1)] : R*) := by
    calc
      squareProbability 1 1 = ε := exercise5_row_probability
      _ = ([(1, -1)] : R*) := rfl
  have hdifference :
      squareProbability M 0 - squareProbability 1 1 =
        ([(-1, -1), (M, -2)] : R*) := by
    rw [hpoints, hrow]
    show merge ([(M, -2)] : R*) (Neg.neg ([(1, -1)] : R*)) = _
    show simplify ([(M, -2)] ++ [(-1, -1)]) =
      ([(-1, -1), (M, -2)] : R*)
    have hs :=
      (simplify_pair (r₁ := (-1 : 𝔽)) (r₂ := M)
        (e₁ := (-1 : ℚ)) (e₂ := (-2 : ℚ))
        (by norm_num) (by norm_num) hM.ne').2
    simpa using hs
  exact lt_of_lead_pair hdifference (by norm_num) (by norm_num) hM.ne'
    (by norm_num)

/-! ## Exercise 6 -- near certainty with visible failure -/

/-- Exercise 6: failure at one of `r` excluded outcomes has probability
`r * epsilon`. -/
theorem exercise6_failure_probability (r : 𝔽) :
    finiteProbability r = monomial r (-1) :=
  finiteProbability_eq_monomial r

/-- Exercise 6: the allowed event is exactly the algebraic complement
`1 - r * epsilon`, stated coefficient-wise. -/
theorem exercise6_allowed_probability (r : 𝔽) :
    complement (finiteProbability r) ≡ₐ
      fieldAdd one (fieldNeg (monomial r (-1))) := by
  rw [finiteProbability_eq_monomial]
  intro order
  rfl

/-- Exercise 6: allowed and excluded outcomes partition certainty exactly
at every algebraic coefficient. -/
theorem exercise6_allowed_failure_partition (r : 𝔽) :
    fieldAdd (finiteProbability r) (complement (finiteProbability r)) ≡ₐ
      one :=
  event_complement_partition _

/-- Exercise 6: with a positive number of exclusions, failure remains
strictly possible. -/
theorem exercise6_failure_positive {r : 𝔽} (hr : 0 < r) :
    (0 : R*) < finiteProbability r := by
  have hfailure : finiteProbability r = ([(r, -1)] : R*) := by
    rw [finiteProbability_eq_monomial, monomial_of_ne hr.ne']
  have hdifference :
      (0 : R*) - finiteProbability r = ([(-r, -1)] : R*) := by
    rw [hfailure]
    show merge (0 : R*) (Neg.neg ([(r, -1)] : R*)) = _
    rw [show (0 : R*) = ([] : R*) from rfl, merge_nil_left]
    rfl
  exact lt_of_lead_single hdifference (neg_neg_of_pos hr)

/-! ## Exercise 7 -- conditioning on a finite rare event -/

/-- The probability `k * epsilon` of the conditioning event, packaged as an
exact nonzero monomial denominator. -/
def finiteRareProbabilityCount (k : 𝔽) (hk : k ≠ 0) : NonzeroCount :=
  ⟨⟨k, -1⟩, hk⟩

/-- Exercise 7: canceling the common infinitesimal before taking a standard
part gives `epsilon / (k * epsilon) = 1/k`. -/
theorem exercise7_rare_event_conditioning {k : 𝔽} (hk : k ≠ 0) :
    conditional (finiteProbability 1) (finiteRareProbabilityCount k hk) =
      monomial k⁻¹ 0 := by
  rw [exercise1_singleton_probability]
  unfold conditional finiteRareProbabilityCount NonzeroCount.reciprocalValue
  rw [show ε = monomial 1 (-1) from monomial_one_neg_one.symm]
  rw [monomial_mul one_ne_zero (inv_ne_zero hk)]
  congr 2
  · ring
  · ring

#print axioms exercise1_singleton_probability
#print axioms exercise2_target_singleton_ratio
#print axioms exercise3_inclusion_exclusion
#print axioms exercise4_segment_point_ratio
#print axioms exercise5_rarity_dominance
#print axioms exercise6_allowed_failure_partition
#print axioms exercise7_rare_event_conditioning

end AlgebraicStochasticsBasic
end HyperLists
end Hypers
