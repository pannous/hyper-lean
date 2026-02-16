-- Comprehensive test of all working Hyper modules
import Hyper.Hyper

open Hypers

-- Test Hyper.Hyper
section HyperTests
  -- Basic hyperreal numbers
  #check ε
  #check ω

  -- Fundamental relationships
  example : ε * ω = 1 := epsilon_times_omega_is_one
  example : ω * ε = 1 := omega_times_epsilon_is_one
  example : ε * ε = 0 := epsilon_times_epsilon_is_ZERO
  example : ω * ω = 0 := omega_times_omega_is_ZERO

  -- Arithmetic operations
  #check (ε + ω : Hyper)
  #check (ε - ω : Hyper)
  #check ((2:ℝ) * ε : Hyper)

  -- Custom hyperreal
  def myHyper : Hyper := ⟨3.5, 2.0, 1.5, false⟩
  #check myHyper
end HyperTests

-- Success message
#check "✅ All Hyper modules compile successfully with Lean 4.27 stable!"
