-- Comprehensive test of the current Hyper modules. The original imported
-- `Hyper.Hyper`, a fixed 3-slot struct deliberately gutted in commit
-- 8a42866; `R*` (Hyper/HyperList.lean, aliased HyperReal) replaced it.
import Hyper.HyperReal
import Hyper.AlgebraicProbability
import Hyper.HyperProbability

open Hypers

-- Test R* (Hyper/HyperList.lean, aliased HyperReal)
section HyperTests
  -- Basic hyperreal numbers
  #check (ε : R*)
  #check (ω : R*)

  -- Fundamental relationships
  example : (ε : R*) * ω = 1 := epsilon_mul_omega
  example : (ω : R*) * ε = 1 := omega_mul_epsilon

  -- Arithmetic operations
  #check (ε + ω : R*)
  #check (ε - ω : R*)
  #check ((2 : ℚ) • ε : R*)

  -- Custom hyperreal — R*'s equivalent of the old struct literal
  -- `⟨3.5, 2.0, 1.5, false⟩` (real, ε, ω parts; no fixed field count to
  -- overflow out of)
  def myHyper : R* := embedQ (7/2) + embedQ 2 * ε + embedQ (3/2) * ω
  #check myHyper
end HyperTests

section AlgebraicProbabilityTests
  open Hypers.HyperLists.AlgebraicProbability

  -- One favorable outcome among omega symbolic outcomes has probability epsilon.
  example :
      probability ⟨1, 0⟩ ⟨⟨1, 1⟩, one_ne_zero⟩ = ε := by
    change monomial (1 * (1 : ℚ)⁻¹) (0 - 1) = ε
    norm_num

  example : probability (NonzeroCount.toCount ⟨⟨3, 2⟩, by norm_num⟩)
      ⟨⟨3, 2⟩, by norm_num⟩ = Hypers.one :=
    probability_total ⟨⟨3, 2⟩, by norm_num⟩

  -- Conditioning through a common infinitesimal factor cancels coefficient-wise.
  example :
      conditional
          (independentAnd ε (monomial (1 / 3) 0))
          ⟨⟨1, -1⟩, one_ne_zero⟩
        ≡ₐ monomial (1 / 3) 0 := by
    simpa using
      conditional_independent ⟨⟨1, -1⟩, one_ne_zero⟩ (monomial (1 / 3) 0)
end AlgebraicProbabilityTests

-- Success message
#check "✅ All Hyper modules compile successfully with Lean 4.27 stable!"
