import Hyper.AlgebraicOrder
import Mathlib.Analysis.Real.Pi.Bounds

/-! A finite algebraic dart model for round boards.

The standard disk/ball volume calibrations are geometric inputs. Matching
the coefficients of their parallel-volume polynomials gives the displayed
contents. We verify positive finite observable partitions, not a general
valuation extension to arbitrary curved sets. π is a real coefficient.
-/
noncomputable section
open scoped AlgebraicHyperreal
namespace RoundContent
open AlgebraicHyperreal AlgebraicIntegral GeometricContent
local notation "ε" => epsilon (K := ℝ)
local notation "C" => (RatFunc.C : ℝ →+* H)
local notation "π" => Real.pi

/-- Coefficient matching uses only finite polynomial arithmetic. -/
theorem disk_parallel_polynomial (r t : ℝ) :
    π * (r + t) ^ 2 = π * r ^ 2 + 2 * t * (π * r) + π * t ^ 2 := by ring

theorem ball_parallel_polynomial (r t : ℝ) :
    (4 * π / 3) * (r + t) ^ 3 = (4 * π / 3) * r ^ 3 +
      2 * t * (2 * π * r ^ 2) + π * t ^ 2 * (4 * r) + (4 * π / 3) * t ^ 3 := by
  ring

def disk (r : ℝ) : H := C (π * r ^ 2) + C (π * r) * ε + ε ^ 2
def ball (r : ℝ) : H := C ((4 * π / 3) * r ^ 3) +
  C (2 * π * r ^ 2) * ε + C (4 * r) * ε ^ 2 + ε ^ 3

theorem unit_disk_content : disk 1 = C π + C π * ε + ε ^ 2 := by
  simp only [disk, one_pow, mul_one]

theorem unit_ball_content :
    ball 1 = C (4 * π / 3) + C (2 * π) * ε + 4 * ε ^ 2 + ε ^ 3 := by
  simp only [ball, one_pow, mul_one, map_ofNat]

theorem unit_disk_pos : 0 < disk 1 := by
  rw [unit_disk_content]
  exact add_pos_of_pos_of_nonneg
    (add_pos (constant_pos Real.pi_pos) (mul_pos (constant_pos Real.pi_pos) epsilon_pos))
    (sq_nonneg _)

theorem unit_ball_pos : 0 < ball 1 := by
  rw [unit_ball_content]
  have hε := epsilon_pos (K := ℝ)
  have h₀ := constant_pos (show 0 < 4 * π / 3 by positivity)
  have h₁ := constant_pos (show 0 < 2 * π by positivity)
  positivity

def diskProbability (v : H) : H := v / disk 1
def ballProbability (v : H) : H := v / ball 1

theorem disk_whole : diskProbability (disk 1) = 1 := div_self (ne_of_gt unit_disk_pos)
theorem ball_whole : ballProbability (ball 1) = 1 := div_self (ne_of_gt unit_ball_pos)

theorem disk_point : diskProbability (ε ^ 2) = ε ^ 2 / (C π + C π * ε + ε ^ 2) := by
  rw [diskProbability, unit_disk_content]

theorem disk_diameter : diskProbability (closedSegment 2) =
    (2 * ε + ε ^ 2) / (C π + C π * ε + ε ^ 2) := by
  simp only [diskProbability, unit_disk_content, closedSegment, halfOpenSegment,
    GeometricContent.point, map_ofNat]

theorem ball_point : ballProbability (ε ^ 3) =
    ε ^ 3 / (C (4 * π / 3) + C (2 * π) * ε + 4 * ε ^ 2 + ε ^ 3) := by
  rw [ballProbability, unit_ball_content]

theorem ball_diameter : ballProbability (CubicContent.segment 2) =
    (2 * ε ^ 2 + ε ^ 3) / ball 1 := by
  unfold ballProbability CubicContent.segment closedSegment halfOpenSegment GeometricContent.point
  simp only [map_ofNat]
  congr 1
  ring

theorem ball_equatorial_disk : ballProbability (ε * disk 1) =
    (C π * ε + C π * ε ^ 2 + ε ^ 3) / ball 1 := by
  rw [ballProbability, unit_disk_content]
  congr 1
  ring

/-- Point, diameter minus the point, disk minus the diameter. -/
def diskContext : Context H (Fin 3) where
  content := ![ε ^ 2, 2 * ε, C π + C (π - 2) * ε]
  content_nonneg i := by
    fin_cases i
    · exact sq_nonneg _
    · change 0 ≤ 2 * ε
      have hε := epsilon_pos (K := ℝ)
      positivity
    · change 0 ≤ C π + C (π - 2) * ε
      have hp : 0 ≤ π - 2 := by linarith [Real.pi_gt_three]
      exact add_nonneg (constant_nonneg Real.pi_pos.le)
        (mul_nonneg (constant_nonneg hp) epsilon_pos.le)
  total_pos := by
    have heq : (∑ i : Fin 3, ![ε ^ 2, 2 * ε, C π + C (π - 2) * ε] i) = disk 1 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, unit_disk_content, map_sub, map_ofNat]
      ring
    rw [heq]
    exact unit_disk_pos

/-- Point, diameter remainder, equatorial disk remainder, ball remainder. -/
def ballContext : Context H (Fin 4) where
  content := ![ε ^ 3, 2 * ε ^ 2, C π * ε + C (π - 2) * ε ^ 2,
    C (4 * π / 3) + C π * ε + C (4 - π) * ε ^ 2]
  content_nonneg i := by
    fin_cases i
    · change 0 ≤ ε ^ 3
      have hε := epsilon_pos (K := ℝ)
      positivity
    · change 0 ≤ 2 * ε ^ 2
      positivity
    · change 0 ≤ C π * ε + C (π - 2) * ε ^ 2
      have hp : 0 ≤ π - 2 := by linarith [Real.pi_gt_three]
      exact add_nonneg (mul_nonneg (constant_nonneg Real.pi_pos.le) epsilon_pos.le)
        (mul_nonneg (constant_nonneg hp) (sq_nonneg _))
    · change 0 ≤ C (4 * π / 3) + C π * ε + C (4 - π) * ε ^ 2
      have hp : 0 ≤ 4 * π / 3 := by positivity
      exact add_nonneg
        (add_nonneg (constant_nonneg hp)
          (mul_nonneg (constant_nonneg Real.pi_pos.le) epsilon_pos.le))
        (mul_nonneg (constant_nonneg (sub_nonneg.mpr Real.pi_lt_four.le)) (sq_nonneg _))
  total_pos := by
    have heq : (∑ i : Fin 4, ![ε ^ 3, 2 * ε ^ 2, C π * ε + C (π - 2) * ε ^ 2,
        C (4 * π / 3) + C π * ε + C (4 - π) * ε ^ 2] i) = ball 1 := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, add_zero, unit_ball_content, map_sub, map_mul, map_ofNat]
      ring
    rw [heq]
    exact unit_ball_pos

theorem disk_context_total : diskContext.total = disk 1 := by
  simp only [Context.total, diskContext, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, unit_disk_content, map_sub, map_ofNat]
  ring

theorem ball_context_total : ballContext.total = ball 1 := by
  simp only [Context.total, ballContext, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, unit_ball_content, map_sub,
    map_mul, map_ofNat]
  ring

theorem disk_context_point : diskContext.prob {0} = diskProbability (ε ^ 2) := by
  rw [Context.prob_singleton, disk_context_total]
  rfl

theorem ball_context_point : ballContext.prob {0} = ballProbability (ε ^ 3) := by
  rw [Context.prob_singleton, ball_context_total]
  rfl

theorem disk_context_diameter : diskContext.prob {0, 1} = diskProbability (closedSegment 2) := by
  unfold Context.prob Context.integral
  rw [disk_context_total]
  simp [Context.raw, Context.indicator, diskContext, Fin.sum_univ_succ,
    diskProbability, closedSegment, halfOpenSegment, GeometricContent.point, map_ofNat, add_comm]

theorem ball_context_diameter : ballContext.prob {0, 1} =
    ballProbability (CubicContent.segment 2) := by
  unfold Context.prob Context.integral
  rw [ball_context_total, ball_diameter]
  simp [Context.raw, Context.indicator, ballContext, Fin.sum_univ_succ, add_comm]

theorem ball_context_equator : ballContext.prob {0, 1, 2} = ballProbability (ε * disk 1) := by
  unfold Context.prob Context.integral
  rw [ball_context_total, ball_equatorial_disk]
  simp [Context.raw, Context.indicator, ballContext, Fin.sum_univ_succ, map_sub, map_ofNat]
  congr 1
  ring

/-- Conditioning on the diameter cancels the ambient disk normalization. -/
theorem disk_point_to_diameter :
    diskContext.prob {0} / diskContext.prob {0, 1} = ε / (2 + ε) := by
  rw [disk_context_point, disk_context_diameter, disk_point, disk_diameter]
  have hd : C π + C π * ε + ε ^ 2 ≠ 0 := by
    rw [← unit_disk_content]
    exact ne_of_gt unit_disk_pos
  have he := ne_of_gt (epsilon_pos (K := ℝ))
  have hl : (2 + ε : H) ≠ 0 := ne_of_gt (by linarith [epsilon_pos (K := ℝ)])
  have hn : (2 * ε + ε ^ 2 : H) ≠ 0 := by
    have hp : 2 * ε + ε ^ 2 = ε * (2 + ε) := by ring
    rw [hp]
    exact mul_ne_zero he hl
  rw [div_div_div_cancel_right₀ hd]
  apply (div_eq_div_iff hn hl).mpr
  ring

theorem ball_point_to_diameter :
    ballContext.prob {0} / ballContext.prob {0, 1} = ε / (2 + ε) := by
  rw [ball_context_point, ball_context_diameter, ball_diameter]
  unfold ballProbability
  have hb := ne_of_gt unit_ball_pos
  have he := ne_of_gt (epsilon_pos (K := ℝ))
  have hl : (2 + ε : H) ≠ 0 := ne_of_gt (by linarith [epsilon_pos (K := ℝ)])
  have hn : (2 * ε ^ 2 + ε ^ 3 : H) ≠ 0 := by
    have hp : 2 * ε ^ 2 + ε ^ 3 = ε ^ 2 * (2 + ε) := by ring
    rw [hp]
    exact mul_ne_zero (pow_ne_zero _ he) hl
  rw [div_div_div_cancel_right₀ hb]
  apply (div_eq_div_iff hn hl).mpr
  ring

end RoundContent
