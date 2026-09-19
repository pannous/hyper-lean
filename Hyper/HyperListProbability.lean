import Hyper.HyperListFoundation
import Hyper.RoundContent
import Hyper.CubicContent

/-! Finite-list fraction implementation of the context-sensitive integral.
The interpretation theorem connects actual list arithmetic to the existing API. -/
noncomputable section
open scoped AlgebraicHyperreal
namespace HyperListFoundation
namespace Fraction
variable {K : Type*} [Field K]

def sum : List (Fraction K) → Fraction K
  | [] => ofValue 0
  | f :: fs => plus f (sum fs)

@[simp] theorem value_sum (fs : List (Fraction K)) :
    (sum fs).value = (fs.map value).sum := by
  induction fs with
  | nil => simp [sum]
  | cons f fs ih => simp [sum, ih]

variable [LinearOrder K] [IsStrictOrderedRing K]
variable {ι : Type*} [Fintype ι]

/-- The denominator is accumulated from the region contents as finite lists. -/
def contextTotal (Ω : AlgebraicIntegral.Context (RatFunc K) ι) : Fraction K :=
  sum (Finset.univ.toList.map fun i => ofValue (Ω.content i))

@[simp] theorem value_contextTotal (Ω : AlgebraicIntegral.Context (RatFunc K) ι) :
    (contextTotal Ω).value = Ω.total := by
  simp [contextTotal, AlgebraicIntegral.Context.total, List.map_map]

def contextRaw (Ω : AlgebraicIntegral.Context (RatFunc K) ι) (f : ι → RatFunc K) : Fraction K :=
  sum (Finset.univ.toList.map fun i => times (ofValue (f i)) (ofValue (Ω.content i)))

@[simp] theorem value_contextRaw (Ω : AlgebraicIntegral.Context (RatFunc K) ι)
    (f : ι → RatFunc K) : (contextRaw Ω f).value = Ω.raw f := by
  simp [contextRaw, AlgebraicIntegral.Context.raw, List.map_map]

/-- Add products of list fractions, then swap the nonzero total's lists. -/
def contextIntegral (Ω : AlgebraicIntegral.Context (RatFunc K) ι)
    (f : ι → RatFunc K) : Fraction K :=
  times (contextRaw Ω f) (reciprocal (contextTotal Ω)
    (by simpa using Ω.total_ne_zero))

theorem value_contextIntegral (Ω : AlgebraicIntegral.Context (RatFunc K) ι)
    (f : ι → RatFunc K) : (contextIntegral Ω f).value = Ω.integral f := by
  simp [contextIntegral, AlgebraicIntegral.Context.integral, div_eq_mul_inv]

theorem contextIntegral_one (Ω : AlgebraicIntegral.Context (RatFunc K) ι) :
    (contextIntegral Ω (fun _ => 1)).value = 1 := by
  rw [value_contextIntegral, AlgebraicIntegral.Context.integral_one]

end Fraction

/-- Sparse, readable presentations rather than reconstructed numerator polynomials. -/
def epsilonTerms : Terms ℝ := [(1, -1)]
def intervalTerms : Terms ℝ := [(1, 0), (1, -1)]
def diskTerms : Terms ℝ := [(Real.pi, 0), (Real.pi, -1), (1, -2)]
def ballTerms : Terms ℝ :=
  [(4 * Real.pi / 3, 0), (2 * Real.pi, -1), (4, -2), (1, -3)]

@[simp] theorem eval_epsilonTerms : eval epsilonTerms = AlgebraicHyperreal.epsilon := by
  simp [epsilonTerms, AlgebraicHyperreal.epsilon, AlgebraicHyperreal.omega]

@[simp] theorem eval_intervalTerms :
    eval intervalTerms = 1 + AlgebraicHyperreal.epsilon := by
  simp [intervalTerms, eval, AlgebraicHyperreal.epsilon, AlgebraicHyperreal.omega]

@[simp] theorem eval_diskTerms : eval diskTerms = RoundContent.disk 1 := by
  simp [diskTerms, eval, RoundContent.disk, AlgebraicHyperreal.epsilon,
    AlgebraicHyperreal.omega, zpow_neg, inv_pow, add_assoc]
  rfl

@[simp] theorem eval_ballTerms : eval ballTerms = RoundContent.ball 1 := by
  simp [ballTerms, eval, RoundContent.ball, AlgebraicHyperreal.epsilon,
    AlgebraicHyperreal.omega, zpow_neg, inv_pow, map_mul, map_div₀, add_assoc]
  rfl

def calibratedPoint : Fraction ℝ where
  numerator := epsilonTerms
  denominator := intervalTerms
  denominator_ne_zero := by
    rw [eval_intervalTerms]
    exact ne_of_gt (add_pos zero_lt_one AlgebraicHyperreal.epsilon_pos)

theorem calibratedPoint_value :
    calibratedPoint.value = AlgebraicHyperreal.epsilon / (1 + AlgebraicHyperreal.epsilon) := by
  simp [Fraction.value, calibratedPoint]

theorem squareTerms_value : eval (mul intervalTerms intervalTerms) = GeometricContent.squareContent := by
  simp only [eval_mul, eval_intervalTerms]
  rw [GeometricContent.square_content, pow_two]

theorem cubeTerms_value : eval (mul (mul intervalTerms intervalTerms) intervalTerms) = CubicContent.cube := by
  simp [CubicContent.cube, CubicContent.box, CubicContent.interval]

end HyperListFoundation
