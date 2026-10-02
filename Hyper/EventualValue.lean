import Hyper.OrderedRational
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Order.Filter.Germ.Basic

/-! Reading the algebraic hyperreals ℝ(ω) at a concrete large real `s` in place of ω.
Every element becomes an eventually defined, eventually continuous real function;
`toGerm` makes this a ring homomorphism into germs at `+∞`. -/

noncomputable section
namespace EventualValue
open Polynomial Filter AlgebraicHyperreal
open scoped AlgebraicHyperreal

abbrev Hyperreal := RatFunc ℝ

/-- The hyperreal `x` read at a concrete real `s` in place of ω. -/
def valueAt (x : Hyperreal) (s : ℝ) : ℝ := x.num.eval s / x.denom.eval s

/-! ### Polynomials have an eventual sign -/

theorem eventually_pos_of_leadingCoeff_pos {p : ℝ[X]} (h : 0 < p.leadingCoeff) :
    ∀ᶠ s in atTop, 0 < p.eval s := by
  by_cases hdeg : 0 < p.degree
  · exact (tendsto_atTop_of_leadingCoeff_nonneg p hdeg h.le).eventually_gt_atTop 0
  · have hn : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (not_lt.mp hdeg)
    refine Eventually.of_forall fun s => ?_
    rw [eq_C_of_natDegree_eq_zero hn, eval_C]
    simpa [leadingCoeff, hn] using h

theorem eventually_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : ∀ᶠ s in atTop, p.eval s ≠ 0 := by
  rcases lt_or_gt_of_ne (leadingCoeff_ne_zero.mpr hp) with h | h
  · filter_upwards [eventually_pos_of_leadingCoeff_pos (p := -p) (by simpa using h)]
      with s hs
    simp only [eval_neg, neg_pos] at hs
    exact hs.ne
  · filter_upwards [eventually_pos_of_leadingCoeff_pos h] with s hs using hs.ne'

theorem eventually_denom_ne_zero (x : Hyperreal) : ∀ᶠ s in atTop, x.denom.eval s ≠ 0 :=
  eventually_ne_zero (RatFunc.denom_ne_zero x)

/-! ### Reading at `s` is eventually a field homomorphism -/

/-- Any fraction representing `x` gives its value, for large enough `s`. -/
theorem eventually_valueAt_eq_div {x : Hyperreal} {p q : ℝ[X]} (hq : q ≠ 0)
    (hx : x = algebraMap ℝ[X] Hyperreal p / algebraMap ℝ[X] Hyperreal q) :
    ∀ᶠ s in atTop, valueAt x s = p.eval s / q.eval s := by
  have injective := RatFunc.algebraMap_injective ℝ
  have hcross : x.num * q = p * x.denom := by
    apply injective
    rw [← RatFunc.num_div_denom x, div_eq_div_iff
      ((map_ne_zero_iff _ injective).mpr (RatFunc.denom_ne_zero x))
      ((map_ne_zero_iff _ injective).mpr hq)] at hx
    simpa only [map_mul] using hx
  filter_upwards [eventually_ne_zero hq, eventually_denom_ne_zero x] with s hqs hds
  rw [valueAt, div_eq_div_iff hds hqs]
  simpa only [eval_mul] using congrArg (eval s) hcross

/-- `x` as the quotient of its own numerator and denominator. -/
theorem num_div_denom' (x : Hyperreal) :
    x = algebraMap ℝ[X] Hyperreal x.num / algebraMap ℝ[X] Hyperreal x.denom :=
  (RatFunc.num_div_denom x).symm

theorem valueAt_const (r : ℝ) (s : ℝ) : valueAt (RatFunc.C r) s = r := by
  simp [valueAt]

theorem valueAt_zero (s : ℝ) : valueAt 0 s = 0 := by simp [valueAt]

theorem eventually_valueAt_add (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (x + y) s = valueAt x s + valueAt y s := by
  have hdx := RatFunc.denom_ne_zero x
  have hdy := RatFunc.denom_ne_zero y
  have hsum : x + y = algebraMap ℝ[X] Hyperreal (x.num * y.denom + x.denom * y.num) /
      algebraMap ℝ[X] Hyperreal (x.denom * y.denom) := by
    conv_lhs => rw [num_div_denom' x, num_div_denom' y]
    rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hdx) (RatFunc.algebraMap_ne_zero hdy)]
    simp only [map_add, map_mul]
  filter_upwards [eventually_valueAt_eq_div (mul_ne_zero hdx hdy) hsum,
    eventually_denom_ne_zero x, eventually_denom_ne_zero y] with s h hxs hys
  rw [h, valueAt, valueAt, div_add_div _ _ hxs hys]
  simp only [eval_add, eval_mul]

theorem eventually_valueAt_mul (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (x * y) s = valueAt x s * valueAt y s := by
  have hprod : x * y = algebraMap ℝ[X] Hyperreal (x.num * y.num) /
      algebraMap ℝ[X] Hyperreal (x.denom * y.denom) := by
    conv_lhs => rw [num_div_denom' x, num_div_denom' y]
    rw [div_mul_div_comm]
    simp only [map_mul]
  filter_upwards [eventually_valueAt_eq_div
    (mul_ne_zero (RatFunc.denom_ne_zero x) (RatFunc.denom_ne_zero y)) hprod] with s h
  rw [h, valueAt, valueAt, div_mul_div_comm]
  simp only [eval_mul]

theorem eventually_valueAt_neg (x : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (-x) s = -valueAt x s := by
  have hneg : -x = algebraMap ℝ[X] Hyperreal (-x.num) / algebraMap ℝ[X] Hyperreal x.denom := by
    conv_lhs => rw [num_div_denom' x]
    rw [map_neg, neg_div]
  filter_upwards [eventually_valueAt_eq_div (RatFunc.denom_ne_zero x) hneg] with s h
  rw [h, valueAt, eval_neg, neg_div]

theorem eventually_valueAt_sub (x y : Hyperreal) :
    ∀ᶠ s in atTop, valueAt (y - x) s = valueAt y s - valueAt x s := by
  filter_upwards [eventually_valueAt_add y (-x), eventually_valueAt_neg x] with s hadd hneg
  rw [sub_eq_add_neg, hadd, hneg, ← sub_eq_add_neg]

/-! ### The order of ℝ(ω) is the eventual order -/

theorem eventually_valueAt_pos {x : Hyperreal} (hx : 0 < x) :
    ∀ᶠ s in atTop, 0 < valueAt x s := by
  rw [pos_iff] at hx
  have hd : 0 < x.denom.leadingCoeff := by simp [(RatFunc.monic_denom x).leadingCoeff]
  filter_upwards [eventually_pos_of_leadingCoeff_pos hx, eventually_pos_of_leadingCoeff_pos hd]
    with s hn hds using div_pos hn hds

theorem eventually_valueAt_lt {x y : Hyperreal} (hxy : x < y) :
    ∀ᶠ s in atTop, valueAt x s < valueAt y s := by
  filter_upwards [eventually_valueAt_pos (sub_pos.mpr hxy), eventually_valueAt_sub x y]
    with s hpos hsub
  rw [hsub] at hpos
  exact sub_pos.mp hpos

theorem eventually_valueAt_ne_zero {x : Hyperreal} (hx : x ≠ 0) :
    ∀ᶠ s in atTop, valueAt x s ≠ 0 := by
  filter_upwards [eventually_ne_zero (RatFunc.num_ne_zero hx), eventually_denom_ne_zero x]
    with s hn hd using div_ne_zero hn hd

theorem eventually_continuousAt_valueAt (x : Hyperreal) :
    ∀ᶠ s in atTop, ContinuousAt (valueAt x) s := by
  filter_upwards [eventually_denom_ne_zero x] with s hd
  exact (x.num.continuousAt).div x.denom.continuousAt hd

/-- ℝ(ω) as germs at `+∞`: ω becomes the identity function. -/
def toGerm : Hyperreal →+* Germ (atTop : Filter ℝ) ℝ where
  toFun x := ↑(valueAt x)
  map_one' := congrArg _ (funext fun s => by simp [valueAt])
  map_zero' := congrArg _ (funext valueAt_zero)
  map_add' x y := by
    rw [← Germ.coe_add]
    exact Germ.coe_eq.mpr (eventually_valueAt_add x y)
  map_mul' x y := by
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.mpr (eventually_valueAt_mul x y)

end EventualValue
