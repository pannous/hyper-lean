import Hyper.AlgebraicDart
import Hyper.AlgebraicSupport
import Hyper.GeometricContent
import Hyper.CubicContent
import Hyper.AlgebraicOrder

/-! Regression and trust-boundary checks for the exact algebraic path only.
Do not import HyperList here: no legacy field axiom may enter these proofs. -/
open scoped AlgebraicHyperreal AlgebraicIntegral
open AlgebraicHyperreal AlgebraicIntegral

noncomputable section
abbrev AH := RatFunc ℝ
local notation "ε" => epsilon (K := ℝ)
local notation "ω" => omega (K := ℝ)

example : (ε : AH) > 0 := epsilon_pos
example : (ε : AH) < RatFunc.C (1 / 1000000 : ℝ) := epsilon_lt_constant (by norm_num)
example : (ε : AH) * ω = 1 := epsilon_mul_omega
example : (1 + ε : AH) * (1 + ε)⁻¹ = 1 := mixed_inverse
example : (ω + 1 : AH)⁻¹ = ε / (1 + ε) := closed_interval_point

-- Exact polynomial moments: evaluate finite power-sum identities at ω.
def S1 (n : AH) := n * (n - 1) / 2
def S2 (n : AH) := n * (n - 1) * (2 * n - 1) / 6

theorem midpoint_first_moment : (S1 ω + ω / 2) * ε ^ 2 = (1 / 2 : AH) := by
  unfold S1 epsilon
  field_simp [omega_ne_zero]
  ring

theorem midpoint_second_moment :
    (S2 ω + S1 ω + ω / 4) * ε ^ 3 = (1 / 3 : AH) - ε ^ 2 / 12 := by
  unfold S1 S2 epsilon
  field_simp [omega_ne_zero]
  ring

theorem midpoint_variance :
    ((1 / 3 : AH) - ε ^ 2 / 12) - (1 / 2 : AH) ^ 2 = (1 - ε ^ 2) / 12 := by ring

theorem mixed_alternatives_normalize :
    (1 / (1 + ε) : AH) + ε / (1 + ε) = 1 := by
  have h : (1 + ε : AH) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  field_simp

-- A normalized dot averages. It does not evaluate every function at a point.
def twoCell : Context AH Bool where
  content := fun _ => 1
  content_nonneg := fun _ => zero_le_one
  total_pos := by norm_num [Fintype.sum_bool]

example : ∫[twoCell] (fun _ => (1 : AH)) = 1 := twoCell.integral_one
example : ∫[twoCell; Finset.univ] (fun _ => (1 : AH)) = 1 := by
  simp [Context.restricted, Context.indicator]
example : ∫[twoCell | Finset.univ] (fun _ => (1 : AH)) = 1 :=
  twoCell.conditional_one (twoCell.prob_univ ▸ one_ne_zero)

example : twoCell.integral (fun b => if b then (2 : AH) else 0) = 1 := by
  norm_num [Context.integral, Context.raw, Context.total, twoCell, Fintype.sum_bool]

-- Product integration is exercised on a nonconstant observable.
example : (twoCell.product twoCell).integral
    (fun ij => if ij.1 = ij.2 then (1 : AH) else 0) = 1 / 2 := by
  simp only [Context.integral, Context.raw, Context.total, Context.product, twoCell,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

#print axioms AlgebraicHyperreal.epsilon_lt_constant
#print axioms AlgebraicSupport.point_ne_dot
#print axioms AlgebraicSupport.dot_ne_halo
#print axioms AlgebraicHyperreal.closed_interval_point
#print axioms Context.integral_nonneg
#print axioms Context.prob_union_inter
#print axioms Context.prob_compl
#print axioms Context.prob_le_one
#print axioms Context.refinement_invariant
#print axioms Context.withDensity_integral
#print axioms Context.fubini
#print axioms Context.integral_delta
#print axioms Context.delta_average
#print axioms Context.delta_singleton
#print axioms AlgebraicDart.whole_board
#print axioms AlgebraicDart.Minimal.descending_midpoints
#print axioms AlgebraicDart.Minimal.descending_sample_count
#print axioms AlgebraicDart.Minimal.geometric_descending_count
#print axioms AlgebraicDart.Minimal.whole_square_integral
#print axioms AlgebraicDart.Minimal.line_integral
#print axioms AlgebraicDart.Minimal.point_integral
#print axioms AlgebraicDart.point_strictly_rarer
#print axioms AlgebraicDart.diagonal_to_point_ratio
#print axioms AlgebraicDart.point_given_diagonal
#print axioms AlgebraicDart.diagonal_given_mixed
#print axioms midpoint_first_moment
#print axioms midpoint_second_moment
#print axioms mixed_alternatives_normalize
#print axioms GeometricContent.length_coefficient_forced
#print axioms GeometricContent.rotation_invariant
#print axioms GeometricContent.endpoint_correction_forced
#print axioms GeometricContent.closed_segment_glue
#print axioms GeometricContent.closed_polygon_dissection
#print axioms GeometricContent.open_polygon_dissection
#print axioms GeometricContent.rectangle_product
#print axioms GeometricContent.square_probability
#print axioms GeometricContent.point_probability
#print axioms GeometricContent.horizontal_probability
#print axioms GeometricContent.diagonal_probability
#print axioms GeometricContent.effective_epsilon_lt_epsilon
#print axioms GeometricContent.point_probability_effective
#print axioms GeometricContent.segment_probability_effective
#print axioms GeometricContent.diagonal_more_likely
#print axioms GeometricContent.context_line_probability
#print axioms GeometricContent.context_point_probability
#print axioms GeometricContent.open_segment_pos
#print axioms GeometricContent.half_epsilon_segment_negative
#print axioms CubicContent.box_dissection
#print axioms CubicContent.cube_probability
#print axioms CubicContent.point_probability
#print axioms CubicContent.segment_probability
#print axioms CubicContent.surface_probability
#print axioms CubicContent.unit_segment_probability
#print axioms CubicContent.unit_surface_probability
#print axioms CubicContent.codimension_law
#print axioms CubicContent.cube_context_total
#print axioms CubicContent.cube_integral_product
#print axioms CubicContent.cube_face_probability
#print axioms CubicContent.cube_line_probability
#print axioms CubicContent.cube_point_probability
#print axioms AlgebraicOrder.IsO.add
#print axioms AlgebraicOrder.IsO.mul
#print axioms AlgebraicOrder.IsO.weaken
#print axioms AlgebraicOrder.IsO.div_gauge
#print axioms AlgebraicOrder.isO_iff_scaled
#print axioms AlgebraicOrder.one_not_isO_epsilon
#print axioms AlgebraicOrder.Approx.trans
#print axioms AlgebraicOrder.Approx.mul
#print axioms AlgebraicOrder.Approx.inv
#print axioms AlgebraicOrder.Approx.div_gauge
#print axioms AlgebraicOrder.inverse_one_add
#print axioms AlgebraicOrder.integral_approx_of_uniform_bound
#print axioms AlgebraicOrder.planar_segment
#print axioms AlgebraicOrder.spatial_segment
#print axioms AlgebraicOrder.spatial_surface
#print axioms AlgebraicOrder.cancellation_retains_remainder
