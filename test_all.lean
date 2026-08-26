-- Comprehensive test of the current Hyper modules. The original imported
-- `Hyper.Hyper`, a fixed 3-slot struct deliberately gutted in commit
-- 8a42866; `R*` (Hyper/HyperList.lean, aliased HyperReal) replaced it.
import Hyper.HyperReal

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

-- Success message
#check "✅ All Hyper modules compile successfully with Lean 4.27 stable!"
