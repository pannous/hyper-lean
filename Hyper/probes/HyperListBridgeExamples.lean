import Hyper.HyperListBridge

/-! Compute with lists (`native_decide`), conclude in the root-closed hyperreals. -/

noncomputable section
namespace HyperListBridge.Examples
open HyperListBridge HyperAlgebraic Hypers

def omegaList : HyperList := [(1, 1)]
def sqrtOmegaList : HyperList := [(1, 1 / 2)]
def cancellingList : HyperList := [(1, 0), (-1, 0)]

theorem toNumber_omegaList : toNumber omegaList = HyperAlgebraic.omega := by
  apply Subtype.ext
  rw [coe_toNumber, HyperListBridge.coe_omega]
  congr 1
  funext s
  simp [listValue, termValue, omegaList]

/-- A non-canonical list is still the number 0: equality is semantic. -/
theorem cancellingList_is_zero : toNumber cancellingList = 0 := by
  rw [← toNumber_nil]
  exact toNumber_eq_of_decide _ _ (by native_decide)

/-- √ω < ω, decided on lists. -/
theorem sqrtOmega_lt_omega : toNumber sqrtOmegaList < HyperAlgebraic.omega := by
  rw [← toNumber_omegaList, ← lt_iff_toNumber_lt]
  native_decide

/-- The list `ω^(1/2)` is exactly the symbolic root `√ω` of `HyperAlgebraic`. -/
theorem sqrtOmegaList_is_sqrt : toNumber sqrtOmegaList = HyperAlgebraic.sqrt HyperAlgebraic.omega := by
  have hsquare : toNumber (sqrtOmegaList * sqrtOmegaList) = toNumber omegaList :=
    toNumber_eq_of_decide _ _ (by native_decide)
  have hlistNonneg : 0 ≤ toNumber sqrtOmegaList := (toNumber_nonneg_iff _).mpr (by native_decide)
  have homegaNonneg : 0 ≤ HyperAlgebraic.omega := by
    rw [← toNumber_omegaList]; exact (toNumber_nonneg_iff _).mpr (by native_decide)
  refine (mul_self_inj hlistNonneg (sqrt_nonneg _)).mp ?_
  rw [← toNumber_mul, hsquare, toNumber_omegaList, sqrt_mul_self homegaNonneg]

#print axioms sqrtOmega_lt_omega
#print axioms sqrtOmegaList_is_sqrt
#print axioms cancellingList_is_zero

end HyperListBridge.Examples
