import Hyper.OrderedRational

/-! Points, radius-ε dots, and halos are distinct even in the minimal
ordered rational-function field. No topological or analytic integral is used. -/
noncomputable section
open scoped AlgebraicHyperreal
namespace AlgebraicSupport
open AlgebraicHyperreal
abbrev H := RatFunc ℝ
local notation "ε" => epsilon (K := ℝ)

def dot (y : H) : Set H := {x | |x - y| < ε}
def halo (y : H) : Set H := {x | ∀ r : ℝ, 0 < r → |x - y| < RatFunc.C r}

theorem point_subset_dot (y : H) : {y} ⊆ dot y := by
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  simpa [dot] using (epsilon_pos (K := ℝ))

theorem dot_subset_halo (y : H) : dot y ⊆ halo y := by
  intro x hx r hr
  exact lt_trans hx (epsilon_lt_constant hr)

theorem half_epsilon_in_dot (y : H) : y + ε / 2 ∈ dot y := by
  change |y + ε / 2 - y| < ε
  have he := epsilon_pos (K := ℝ)
  rw [add_sub_cancel_left, abs_of_pos (div_pos he (by norm_num))]
  linarith

theorem half_epsilon_ne_point (y : H) : y + ε / 2 ≠ y := by
  have he := epsilon_pos (K := ℝ)
  intro h
  linarith

theorem two_epsilon_in_halo (y : H) : y + 2 * ε ∈ halo y := by
  intro r hr
  have he := epsilon_pos (K := ℝ)
  have h := epsilon_lt_constant (div_pos hr (show (0 : ℝ) < 2 by norm_num))
  have hc : RatFunc.C (r / 2) = (RatFunc.C r : H) / 2 := by
    simp only [map_div₀, map_ofNat]
  rw [hc] at h
  rw [add_sub_cancel_left, abs_of_pos (mul_pos (by norm_num) he)]
  linarith

theorem two_epsilon_not_in_dot (y : H) : y + 2 * ε ∉ dot y := by
  have he := epsilon_pos (K := ℝ)
  change ¬ |y + 2 * ε - y| < ε
  rw [add_sub_cancel_left, abs_of_pos (mul_pos (by norm_num) he)]
  linarith

theorem point_ne_dot (y : H) : ({y} : Set H) ≠ dot y := by
  intro h
  have hm := half_epsilon_in_dot y
  rw [← h, Set.mem_singleton_iff] at hm
  exact half_epsilon_ne_point y hm

theorem dot_ne_halo (y : H) : dot y ≠ halo y := by
  intro h
  exact two_epsilon_not_in_dot y (h.symm ▸ two_epsilon_in_halo y)

#print axioms point_ne_dot
#print axioms dot_ne_halo
end AlgebraicSupport
