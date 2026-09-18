import Hyper.GeometricContent

/-! Orthogonal products and codimension in algebraic geometric probability.

These proofs extend the standard-coordinate interval and polygon contents.
They do not postulate a content for arbitrary curved surfaces or polyhedra.
The product rule is the existing finite Context product/Fubini rule.
-/
noncomputable section
open scoped AlgebraicHyperreal
namespace CubicContent
open AlgebraicHyperreal AlgebraicIntegral GeometricContent

local notation "ε" => epsilon (K := ℝ)
local notation "η" => effectiveEpsilon
local notation "C" => (RatFunc.C : ℝ →+* H)

def interval (a : ℝ) : H := C a + ε
def box (a b c : ℝ) : H := interval a * interval b * interval c
def point : H := ε ^ 3
def segment (L : ℝ) : H := ε * closedSegment L
def surface (A P : ℝ) : H := ε * closedPolygon A P
def cube : H := box 1 1 1
def probability (v : H) : H := v / cube

theorem box_expansion (a b c : ℝ) :
    box a b c = C (a * b * c) + C (a * b + a * c + b * c) * ε +
      C (a + b + c) * ε ^ 2 + ε ^ 3 := by
  simp only [box, interval, map_add, map_mul]
  ring

theorem cube_content : cube = (1 + ε) ^ 3 := by
  simp only [cube, box, interval, map_one]
  ring

theorem cube_pos : 0 < cube := by
  rw [cube_content]
  exact pow_pos (add_pos zero_lt_one epsilon_pos) _

theorem cube_probability : probability cube = 1 := div_self (ne_of_gt cube_pos)

/-- The cut rectangle is counted twice and subtracted once. -/
theorem box_dissection (a b c d : ℝ) :
    box a c d + box b c d - surface (c * d) (2 * (c + d)) =
      box (a + b) c d := by
  rw [surface, rectangle_product]
  simp only [box, interval, map_add]
  ring

theorem point_probability : probability point = η ^ 3 := by
  simp only [probability, point, cube_content, effectiveEpsilon, div_pow]

theorem segment_probability (L : ℝ) :
    probability (segment L) = C L * η ^ 2 + (1 - C L) * η ^ 3 := by
  unfold probability segment closedSegment halfOpenSegment GeometricContent.point
  rw [cube_content]
  unfold effectiveEpsilon
  have h : (1 + ε : H) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  field_simp
  ring

theorem unit_segment_probability : probability (segment 1) = η ^ 2 := by
  simp [segment_probability]

/-- A closed convex planar patch with standard area A and perimeter P. -/
theorem surface_probability (A P : ℝ) :
    probability (surface A P) = C A * η * (1 - η) ^ 2 +
      C (P / 2) * η ^ 2 * (1 - η) + η ^ 3 := by
  unfold probability surface closedPolygon GeometricContent.point
  rw [cube_content]
  unfold effectiveEpsilon
  have h : (1 + ε : H) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  field_simp
  ring

theorem unit_surface_probability : probability (surface 1 4) = η := by
  rw [surface_probability]
  norm_num
  simp only [map_ofNat]
  ring

/-- free coordinates range over a closed unit interval; fixed coordinates
are singletons. The exponent counts constraints, in every finite dimension. -/
def coordinateProbability (free fixed : ℕ) : H :=
  (1 + ε) ^ free * ε ^ fixed / (1 + ε) ^ (free + fixed)

theorem codimension_law (free fixed : ℕ) :
    coordinateProbability free fixed = η ^ fixed := by
  unfold coordinateProbability effectiveEpsilon
  rw [pow_add, div_pow]
  have h : (1 + ε : H) ≠ 0 := ne_of_gt (add_pos zero_lt_one epsilon_pos)
  field_simp

/-- Two observable regions: a chosen point and the remainder of the unit
interval. The remainder has content 1 by finite subtraction. -/
def coordinateContext : Context H (Fin 2) where
  content := ![ε, 1]
  content_nonneg i := by
    fin_cases i
    · exact (epsilon_pos (K := ℝ)).le
    · exact zero_le_one
  total_pos := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      Matrix.cons_val_succ, add_zero]
    exact add_pos epsilon_pos zero_lt_one

theorem coordinate_total : coordinateContext.total = 1 + ε := by
  simp [Context.total, coordinateContext, Fin.sum_univ_succ, add_comm]

theorem coordinate_point_probability : coordinateContext.prob {0} = η := by
  rw [Context.prob_singleton, coordinate_total]
  rfl

theorem coordinate_indicator_integral :
    coordinateContext.integral (Context.indicator {0}) = η :=
  coordinate_point_probability

def cubeContext := (coordinateContext.product coordinateContext).product coordinateContext

theorem cube_context_total : cubeContext.total = cube := by
  rw [cubeContext, Context.product_total, Context.product_total, coordinate_total,
    cube_content]
  ring

/-- A separable event: its indicator is a product of coordinate indicators. -/
theorem cube_integral_product (f g h : Fin 2 → H) :
    cubeContext.integral (fun ijk => f ijk.1.1 * g ijk.1.2 * h ijk.2) =
      coordinateContext.integral f * coordinateContext.integral g *
        coordinateContext.integral h := by
  unfold cubeContext
  rw [Context.fubini]
  simp_rw [Context.integral_scale]
  rw [Context.fubini]
  simp_rw [mul_assoc, Context.integral_scale]
  have scale_right (q : Fin 2 → H) (a : H) :
      coordinateContext.integral (fun i => q i * a) =
        coordinateContext.integral q * a := by
    simpa only [mul_comm] using coordinateContext.integral_scale a q
  simp_rw [scale_right]

theorem cube_face_probability :
    cubeContext.integral (fun ijk => Context.indicator {0} ijk.1.1) = η := by
  have h := cube_integral_product (Context.indicator {0}) (fun _ => 1) (fun _ => 1)
  simpa only [mul_one, Context.integral_one, coordinate_indicator_integral] using h

theorem cube_line_probability :
    cubeContext.integral (fun ijk =>
      Context.indicator {0} ijk.1.1 * Context.indicator {0} ijk.1.2) = η ^ 2 := by
  have h := cube_integral_product (Context.indicator {0}) (Context.indicator {0}) (fun _ => 1)
  simpa only [mul_one, Context.integral_one, coordinate_indicator_integral, pow_two] using h

theorem cube_point_probability :
    cubeContext.integral (fun ijk => Context.indicator {0} ijk.1.1 *
      Context.indicator {0} ijk.1.2 * Context.indicator {0} ijk.2) = η ^ 3 := by
  have h := cube_integral_product (Context.indicator {0}) (Context.indicator {0})
    (Context.indicator {0})
  simpa only [coordinate_indicator_integral, pow_succ, pow_zero,
    one_mul] using h

end CubicContent
