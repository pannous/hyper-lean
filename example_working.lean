-- Working example with Hyper numbers in Lean 4.27 stable
import Hyper.Hyper

open Hypers

-- Define some hyperreal numbers
def myHyper : Hyper := ⟨3.5, 2.0, 1.5, false⟩

-- Check basic operations
#check epsilon
#check omega
#check ε * ω
#check ε + ω

-- Verify the fundamental relationship
#check epsilon_times_omega_is_one
#check omega_times_epsilon_is_one

-- Note: ε * ε = 0 (infinitesimal squared is zero)
#check epsilon_times_epsilon_is_ZERO

-- Note: ω * ω = 0 (this breaks the field axiom)
#check omega_times_omega_is_ZERO

example : ε * ω = 1 := epsilon_times_omega_is_one
example : ω * ε = 1 := omega_times_epsilon_is_one
example : ε * ε = 0 := epsilon_times_epsilon_is_ZERO
example : ω * ω = 0 := omega_times_omega_is_ZERO
