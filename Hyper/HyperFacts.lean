import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Hyper.HyperKeisler

namespace Hyperreal

-- Theorem 1.3. The set Finite = galaxy(0) of finite elements is a subring of R∗, that
-- is, sums, diﬀerences, and products of finite elements are finite.
theorem galaxy_zero_subring :
  ∀ x y : R*, finite x → finite y → finite (x + y) ∧ finite (x - y) ∧ finite (x * y) :=
by
  intro x y hx hy
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  apply And.intro
  · use r + s
    rw [extension.map_add]  -- Uses RingHom property
    apply lt_of_le_of_lt (abs_add x y)
    exact add_lt_add hr hs
  · apply And.intro
    · use r + s
      rw [extension.map_add]
      apply lt_of_le_of_lt (abs_sub x y)
      exact add_lt_add hr hs
    · use r * s
      rw [extension.map_mul, abs_mul]  -- Uses RingHom property
      apply mul_lt_mul'' hr hs (abs_nonneg x) (abs_nonneg y)
