import Hyper.ContextIntegral

/-! Algebraic geometric content for planar polyhedral data.

The coefficients are standard real geometric data; ε is the formal gauge.
We check length invariance, finite dissection identities, endpoint corrections,
and exact square normalization. The general theorem assigning signatures to
arbitrary geometric polyhedral sets independently of triangulation is not
implemented here; no axiom asserting it is introduced.
-/
noncomputable section
open scoped AlgebraicHyperreal
namespace GeometricContent
open AlgebraicHyperreal AlgebraicIntegral

abbrev H := RatFunc ℝ
local notation "ε" => epsilon (K := ℝ)
local notation "C" => (RatFunc.C : ℝ →+* H)

/-- Euclidean length from the algebraic squared-distance equation. -/
def length (v : ℝ × ℝ) : ℝ := Real.sqrt (v.1 ^ 2 + v.2 ^ 2)

theorem length_squared (v : ℝ × ℝ) : (length v) ^ 2 = v.1 ^ 2 + v.2 ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- An orthogonal rotation preserves length; its input is c²+s²=1. -/
theorem rotation_invariant (x y c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    length (c * x - s * y, s * x + c * y) = length (x, y) := by
  unfold length
  congr 1
  nlinarith [sq_nonneg x, sq_nonneg y,
    show (c * x - s * y) ^ 2 + (s * x + c * y) ^ 2 =
      (c ^ 2 + s ^ 2) * (x ^ 2 + y ^ 2) by ring]

theorem axis_length : length (1, 0) = 1 := by norm_num [length]
theorem diagonal_length : length (1, -1) = Real.sqrt 2 := by norm_num [length]

/-- No direction-specific probability axiom is needed: rotation invariance,
degree-one scaling, and a unit calibration force the coefficient to be length.
This theorem concerns the one-dimensional coefficient, not endpoint terms. -/
theorem length_coefficient_forced (F : ℝ × ℝ → ℝ)
    (hscale : ∀ (r : ℝ), 0 ≤ r → ∀ v : ℝ × ℝ,
      F (r * v.1, r * v.2) = r * F v)
    (hrotate : ∀ (v : ℝ × ℝ) (c s : ℝ), c ^ 2 + s ^ 2 = 1 →
      F (c * v.1 - s * v.2, s * v.1 + c * v.2) = F v)
    (hunit : F (1, 0) = 1) (v : ℝ × ℝ) : F v = length v := by
  rcases v with ⟨x, y⟩
  have hsq := length_squared (x, y)
  by_cases hl : length (x, y) = 0
  · have hz : x ^ 2 + y ^ 2 = 0 := by simpa [hl] using hsq.symm
    have hx : x = 0 := by nlinarith [sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x]
    rw [hl, hx, hy]
    simpa using hscale 0 (by norm_num) (1, 0)
  · have hrot : (x / length (x, y)) ^ 2 + (y / length (x, y)) ^ 2 = 1 := by
      field_simp
      nlinarith [hsq]
    have hf := hrotate (1, 0) (x / length (x, y)) (y / length (x, y)) hrot
    simp only [mul_one, mul_zero, sub_zero, add_zero, hunit] at hf
    have hs := hscale (length (x, y)) (Real.sqrt_nonneg _)
      (x / length (x, y), y / length (x, y))
    have hx : length (x, y) * (x / length (x, y)) = x := by field_simp
    have hy : length (x, y) * (y / length (x, y)) = y := by field_simp
    simpa only [hx, hy, hf, mul_one] using hs

def point : H := ε ^ 2
def halfOpenSegment (L : ℝ) : H := C L * ε
def closedSegment (L : ℝ) : H := halfOpenSegment L + point
def openSegment (L : ℝ) : H := halfOpenSegment L - point

/-- Closed convex polygon: area + half-perimeter ε + ε². -/
def closedPolygon (A P : ℝ) : H := C A + C (P / 2) * ε + point
/-- Interior of that polygon. Lower-dimensional boundary terms change sign. -/
def openPolygon (A P : ℝ) : H := C A - C (P / 2) * ε + point

/-- The lower-order correction is forced by gluing at one point. -/
theorem endpoint_correction_forced (a b : H) (k : H)
    (h : (a + b) * ε + k = (a * ε + k) + (b * ε + k) - point) :
    k = point := by
  linear_combination -h

theorem closed_segment_glue (a b : ℝ) :
    closedSegment a + closedSegment b - point = closedSegment (a + b) := by
  simp only [closedSegment, halfOpenSegment, map_add]
  ring

theorem open_segment_split (a b : ℝ) :
    openSegment a + point + openSegment b = openSegment (a + b) := by
  simp only [openSegment, halfOpenSegment, map_add]
  ring

theorem remove_endpoint (L : ℝ) : closedSegment L - point = halfOpenSegment L := by
  simp [closedSegment]

/-- The shared cut has length L. Its two perimeter appearances cancel. -/
theorem closed_polygon_dissection (A₁ A₂ P₁ P₂ L : ℝ) :
    closedPolygon A₁ P₁ + closedPolygon A₂ P₂ - closedSegment L =
      closedPolygon (A₁ + A₂) (P₁ + P₂ - 2 * L) := by
  simp only [closedPolygon, closedSegment, halfOpenSegment, map_add, map_sub,
    map_div₀, map_mul, map_ofNat]
  ring

theorem open_polygon_dissection (A₁ A₂ P₁ P₂ L : ℝ) :
    openPolygon A₁ P₁ + openPolygon A₂ P₂ + openSegment L =
      openPolygon (A₁ + A₂) (P₁ + P₂ - 2 * L) := by
  simp only [openPolygon, openSegment, halfOpenSegment, map_add, map_sub,
    map_div₀, map_mul, map_ofNat]
  ring

theorem rectangle_product (a b : ℝ) :
    closedPolygon (a * b) (2 * (a + b)) = (C a + ε) * (C b + ε) := by
  simp only [closedPolygon, point, map_add, map_div₀, map_mul, map_ofNat]
  ring

def squareContent : H := closedPolygon 1 4

theorem square_content : squareContent = (1 + ε) ^ 2 := by
  norm_num [squareContent, closedPolygon, point]
  simp only [map_ofNat]
  ring

theorem square_content_pos : 0 < squareContent := by
  rw [square_content]
  exact sq_pos_of_pos (add_pos zero_lt_one epsilon_pos)

def probability (content : H) : H := content / squareContent

theorem square_probability : probability squareContent = 1 :=
  div_self (ne_of_gt square_content_pos)

theorem point_probability : probability point = ε ^ 2 / (1 + ε) ^ 2 := by
  rw [probability, square_content, point]

theorem segment_probability (L : ℝ) :
    probability (closedSegment L) = (C L * ε + ε ^ 2) / (1 + ε) ^ 2 := by
  rw [probability, square_content, closedSegment, halfOpenSegment, point]

theorem horizontal_probability :
    probability (closedSegment (length (1, 0))) = ε / (1 + ε) := by
  rw [axis_length, segment_probability]
  have h : (1 + ε : H) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  simp only [map_one]
  field_simp

theorem diagonal_probability :
    probability (closedSegment (length (1, -1))) =
      (C (Real.sqrt 2) * ε + ε ^ 2) / (1 + ε) ^ 2 := by
  rw [diagonal_length, segment_probability]

/-- The normalized square's effective one-coordinate resolution. -/
def effectiveEpsilon : H := ε / (1 + ε)

theorem effective_epsilon_pos : 0 < effectiveEpsilon :=
  div_pos epsilon_pos (add_pos zero_lt_one epsilon_pos)

theorem effective_epsilon_lt_epsilon : effectiveEpsilon < ε :=
  div_lt_self epsilon_pos (lt_add_of_pos_right 1 epsilon_pos)

theorem point_probability_effective : probability point = effectiveEpsilon ^ 2 := by
  rw [point_probability]
  simp [effectiveEpsilon, div_pow]

theorem segment_probability_effective (L : ℝ) :
    probability (closedSegment L) =
      C L * effectiveEpsilon + (1 - C L) * effectiveEpsilon ^ 2 := by
  rw [segment_probability]
  unfold effectiveEpsilon
  have h : (1 + ε : H) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  field_simp
  ring

/-- Equal endpoint conventions leave a purely length-dependent difference. -/
theorem segment_probability_difference (a b : ℝ) :
    probability (closedSegment a) - probability (closedSegment b) =
      C (a - b) * ε / squareContent := by
  simp only [probability, closedSegment, halfOpenSegment, map_sub]
  ring

/-- Both finite-geometry invariance and endpoint correction are essential:
without the correction, two closed unit segments contradict point positivity. -/
theorem uncorrected_closed_segments_impossible :
    (2 : H) * ε ≠ ε + ε - point := by
  have hp : 0 < point := sq_pos_of_pos (epsilon_pos (K := ℝ))
  intro h
  linarith

theorem constant_pos {r : ℝ} (hr : 0 < r) : 0 < C r := by
  rw [AlgebraicHyperreal.pos_iff]
  simpa using hr

theorem constant_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ C r := by
  rw [AlgebraicHyperreal.nonneg_iff]
  simpa using hr

theorem diagonal_more_likely :
    probability (closedSegment (length (1, 0))) <
      probability (closedSegment (length (1, -1))) := by
  rw [axis_length, diagonal_length, ← sub_pos, segment_probability_difference]
  have hs : 1 < Real.sqrt 2 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hp := Real.sqrt_nonneg 2
    nlinarith
  exact div_pos (mul_pos (constant_pos (sub_pos.mpr hs)) epsilon_pos) square_content_pos

/-- Point on a closed segment, the remainder of that segment, and the rest
of a closed unit square. For actual segments inside the square, L ≤ √2 < 2.
The upper bound used here is sufficient for the algebraic positivity proof. -/
def squareContext (L : ℝ) (hL : 0 < L) (hL2 : L ≤ 2) : Context H (Fin 3) where
  content := ![point, halfOpenSegment L, 1 + C (2 - L) * ε]
  content_nonneg i := by
    fin_cases i
    · change 0 ≤ point
      exact sq_nonneg ε
    · change 0 ≤ C L * ε
      exact mul_nonneg (constant_pos hL).le (epsilon_pos (K := ℝ)).le
    · change 0 ≤ 1 + C (2 - L) * ε
      exact add_nonneg zero_le_one (mul_nonneg (constant_nonneg (sub_nonneg.mpr hL2))
        (epsilon_pos (K := ℝ)).le)
  total_pos := by
    have heq : (∑ i : Fin 3, ![point, halfOpenSegment L, 1 + C (2 - L) * ε] i) =
        squareContent := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, halfOpenSegment, map_sub, map_ofNat]
      rw [square_content]
      unfold point
      ring
    rw [heq]
    exact square_content_pos

theorem context_total (L : ℝ) (hL : 0 < L) (hL2 : L ≤ 2) :
    (squareContext L hL hL2).total = squareContent := by
  simp only [Context.total, squareContext, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, halfOpenSegment, map_sub, map_ofNat]
  rw [square_content]
  unfold point
  ring

theorem context_point_probability (L : ℝ) (hL : 0 < L) (hL2 : L ≤ 2) :
    (squareContext L hL hL2).prob {0} = probability point := by
  rw [Context.prob_singleton, context_total]
  rfl

theorem context_line_probability (L : ℝ) (hL : 0 < L) (hL2 : L ≤ 2) :
    (squareContext L hL hL2).prob {0, 1} = probability (closedSegment L) := by
  unfold Context.prob Context.integral
  rw [context_total]
  simp [Context.raw, Context.indicator, squareContext, Fin.sum_univ_succ,
    probability, closedSegment, add_comm]

/-- The open-segment content is positive for every positive STANDARD length.
This is not a claim for ε-dependent geometric lengths. -/
theorem open_segment_pos {L : ℝ} (hL : 0 < L) : 0 < openSegment L := by
  have he := epsilon_pos (K := ℝ)
  have h := epsilon_lt_constant hL
  have hp := mul_pos he (sub_pos.mpr h)
  simpa only [openSegment, halfOpenSegment, point, mul_sub, pow_two, mul_comm] using hp

/-- An infinitesimal geometric length cannot be substituted into the
standard-polyhedral positivity theorem. This counterexample guards scope. -/
theorem half_epsilon_segment_negative : (ε / 2) * ε - point < 0 := by
  have he := epsilon_pos (K := ℝ)
  unfold point
  nlinarith [sq_pos_of_pos he]

end GeometricContent
