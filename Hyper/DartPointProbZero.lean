/-
  Hyperreal dart probabilities, proved on the concrete HyperList model.
  ======================================================================

  Classically, a dart landing uniformly at random on a disc of area A has
  probability 0 of hitting any single point, and probability 0 of landing
  exactly on any single line through the disc.  Both are classically null,
  even though the dart has to land at some point.

  Here probability is computed by normalized algebraic counting:
    • hitting a specific point  has probability ε² / A   (order-2 infinitesimal)
    • hitting a specific line   has probability L·ε / A   (order-1 infinitesimal,
      L the line's 1-D "length" relative to the disc)

  Both are positive, and both have standard coefficient 0. The line
  is infinitely more probable than the point: line/point = L·ω.

  This mirrors `HyperProbability.lean`, but everything below is a proved
  theorem on the executable `R* = HyperList` model (Hyper/HyperList.lean)
  rather than an axiom on an opaque `HReal`. Since HyperList's scalar field
  is ℚ (not ℝ — see the `𝔽 := ℚ` choice in HyperList.lean), the disc's area
  `A` and the line's length `L` are rational parameters here rather than
  literally `π R²`; the ε/ε² dimensional structure is exactly the same.
-/
import Hyper.AlgebraicProbability

namespace Hypers
namespace HyperLists

open AlgebraicProbability

-- ═══════════════════════════════════════════════════════════════════════════
-- A single helper: multiplying two monomials (singleton hyperreals).
-- ═══════════════════════════════════════════════════════════════════════════

lemma embedQ_inv {r : 𝔽} (_h : r ≠ 0) : (embedQ r)⁻¹ = embedQ r⁻¹ := by
  show ([(r, 0)] : R*).map (fun p => (p.1⁻¹, -p.2)) = [(r⁻¹, 0)]
  simp

lemma embedQ_mul_epsilon {r : 𝔽} (h : r ≠ 0) : embedQ r * ε = ([(r, -1)] : R*) := by
  show normalize (([(r, 0)] : List (𝔽 × 𝔽)).product [(1, -1)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, h]

lemma epsilon_sq_eq : ε * ε = ([(1, -2)] : R*) := by
  show normalize (([(1, -1)] : List (𝔽 × 𝔽)).product [(1, -1)] |>.map _) = _
  norm_num [normalize, simplify, mergeAdjacent, List.product]

-- ═══════════════════════════════════════════════════════════════════════════
-- Algebraic dart probabilities for a region with normalization coefficient A.
-- ═══════════════════════════════════════════════════════════════════════════

/-- Probability of one specified grid outcome among `A·ω²` outcomes. -/
def pointProbability (A : ℚ) : R* := (ε * ε) * (embedQ A)⁻¹

/-- Probability of a line containing `L·ω` grid outcomes among `A·ω²`. -/
def lineProbability (L A : ℚ) : R* := (embedQ L * ε) * (embedQ A)⁻¹

lemma pointProbability_eq {A : ℚ} (hA : A ≠ 0) :
    pointProbability A = ([(A⁻¹, -2)] : R*) := by
  show (ε * ε) * (embedQ A)⁻¹ = _
  rw [epsilon_sq_eq, embedQ_inv hA]
  show normalize (([(1, -2)] : List (𝔽 × 𝔽)).product [(A⁻¹, 0)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, inv_ne_zero hA]

lemma lineProbability_eq {L A : ℚ} (hL : L ≠ 0) (hA : A ≠ 0) :
    lineProbability L A = ([(L * A⁻¹, -1)] : R*) := by
  show (embedQ L * ε) * (embedQ A)⁻¹ = _
  rw [embedQ_mul_epsilon hL, embedQ_inv hA]
  show normalize (([(L, -1)] : List (𝔽 × 𝔽)).product [(A⁻¹, 0)] |>.map _) = _
  simp [normalize, simplify, mergeAdjacent, List.product, mul_ne_zero hL (inv_ne_zero hA)]

/-- The point formula is derived from one favorable outcome among `A·ω²`. -/
theorem pointProbability_from_counts {A : ℚ} (hA : A ≠ 0) :
    pointProbability A = probability ⟨1, 0⟩ ⟨⟨A, 2⟩, hA⟩ := by
  rw [pointProbability_eq hA]
  unfold probability
  change ([(A⁻¹, -2)] : R*) = monomial (1 * A⁻¹) (0 - 2)
  simp [monomial, inv_ne_zero hA]

/-- The line formula is derived from `L·ω` favorable outcomes among `A·ω²`. -/
theorem lineProbability_from_counts {L A : ℚ} (hL : L ≠ 0) (hA : A ≠ 0) :
    lineProbability L A = probability ⟨L, 1⟩ ⟨⟨A, 2⟩, hA⟩ := by
  rw [lineProbability_eq hL hA]
  unfold probability
  change ([(L * A⁻¹, -1)] : R*) = monomial (L * A⁻¹) (1 - 2)
  simp [monomial, mul_ne_zero hL (inv_ne_zero hA)]
  norm_num

-- ═══════════════════════════════════════════════════════════════════════════
-- Main theorems: possible (> 0), invisible classically (st = 0), and the
-- line is infinitely more probable than the point.
-- ═══════════════════════════════════════════════════════════════════════════

/-- A point has positive hyperreal probability although its standard
    coefficient is zero. -/
theorem point_prob_pos {A : ℚ} (hA : 0 < A) : 0 < pointProbability A := by
  have hAi : (0:ℚ) < A⁻¹ := inv_pos.mpr hA
  have hab : (0 : R*) - pointProbability A = ([(-A⁻¹, -2)] : R*) := by
    rw [pointProbability_eq hA.ne']
    show Sub.sub (0 : R*) ([(A⁻¹, -2)] : R*) = _
    show merge (0 : R*) (Neg.neg ([(A⁻¹, -2)] : R*)) = _
    rw [show (0 : R*) = ([] : R*) from rfl, merge_nil_left]
    rfl
  exact lt_of_lead_single hab (neg_neg_of_pos hAi)

/-- A line segment also has positive hyperreal probability. -/
theorem line_prob_pos {L A : ℚ} (hL : 0 < L) (hA : 0 < A) :
    0 < lineProbability L A := by
  have hLA : (0:ℚ) < L * A⁻¹ := mul_pos hL (inv_pos.mpr hA)
  have hab : (0 : R*) - lineProbability L A = ([(-(L * A⁻¹), -1)] : R*) := by
    rw [lineProbability_eq hL.ne' hA.ne']
    show Sub.sub (0 : R*) ([(L * A⁻¹, -1)] : R*) = _
    show merge (0 : R*) (Neg.neg ([(L * A⁻¹, -1)] : R*)) = _
    rw [show (0 : R*) = ([] : R*) from rfl, merge_nil_left]
    rfl
  exact lt_of_lead_single hab (neg_neg_of_pos hLA)

/-- The line is *strictly more probable* than the point: ε (order -1) beats
    ε² (order -2) — higher order dominates in the hyperreal order. -/
theorem point_lt_line {L A : ℚ} (hL : 0 < L) (hA : 0 < A) :
    pointProbability A < lineProbability L A := by
  have hAi : (0:ℚ) < A⁻¹ := inv_pos.mpr hA
  have hLA : (0:ℚ) < L * A⁻¹ := mul_pos hL hAi
  have hab : pointProbability A - lineProbability L A
      = ([(-(L * A⁻¹), -1), (A⁻¹, -2)] : R*) := by
    rw [pointProbability_eq hA.ne', lineProbability_eq hL.ne' hA.ne']
    show merge ([(A⁻¹, -2)] : R*) (Neg.neg ([(L * A⁻¹, -1)] : R*)) = _
    show simplify (([(A⁻¹, -2)] : List (𝔽 × 𝔽)) ++ [(-(L * A⁻¹), -1)]) = _
    have := (simplify_pair (r₁ := -(L * A⁻¹)) (r₂ := A⁻¹) (e₁ := -1) (e₂ := -2)
      (by norm_num) (neg_ne_zero.mpr hLA.ne') hAi.ne').2
    simpa using this
  exact lt_of_lead_pair hab (by norm_num) (neg_ne_zero.mpr hLA.ne') hAi.ne' (neg_neg_of_pos hLA)

/-- The standard coefficient of both probabilities is 0. -/
theorem point_prob_standard_zero {A : ℚ} (hA : A ≠ 0) :
    st (pointProbability A) = 0 := by
  rw [pointProbability_eq hA]
  show simplify (List.filter (fun p => p.2 = 0) ([(A⁻¹, -2)] : List (𝔽 × 𝔽))) = _
  norm_num [simplify, mergeAdjacent]
  rfl

theorem line_prob_standard_zero {L A : ℚ} (hL : L ≠ 0) (hA : A ≠ 0) :
    st (lineProbability L A) = 0 := by
  rw [lineProbability_eq hL hA]
  show simplify (List.filter (fun p => p.2 = 0) ([(L * A⁻¹, -1)] : List (𝔽 × 𝔽))) = _
  norm_num [simplify, mergeAdjacent]
  rfl

-- ═══════════════════════════════════════════════════════════════════════════
-- Sanity check: a concrete instance (unit disc, unit-length line).
-- ═══════════════════════════════════════════════════════════════════════════

example : (0:R*) < pointProbability 1 := point_prob_pos one_pos
example : (0:R*) < lineProbability 1 1 := line_prob_pos one_pos one_pos
example : pointProbability 1 < lineProbability 1 1 := point_lt_line one_pos one_pos
example : st (pointProbability 1) = 0 := point_prob_standard_zero one_ne_zero
example : st (lineProbability 1 1) = 0 := line_prob_standard_zero one_ne_zero one_ne_zero

end HyperLists
end Hypers
