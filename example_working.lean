-- Working example with hyperreals in Lean 4.27 stable, updated for the
-- current `R*` model (Hyper/HyperList.lean). The original imported
-- `Hyper.Hyper`, a fixed 3-slot struct deliberately gutted in commit
-- 8a42866; `R*` (`List (ℚ × ℚ)`) replaced it.
import Hyper.HyperReal

open Hypers

-- Define some hyperreal numbers
def myHyper : R* := embedQ 3 + embedQ (7/2) * ε -- 3 + 3.5ε, `R*`'s equivalent shape

-- Check basic operations
#check (ε : R*)
#check (ω : R*)
#check (ε * ω : R*)
#check (ε + ω : R*)

-- Verify the fundamental relationship
example : (ε : R*) * ω = 1 := epsilon_mul_omega
example : (ω : R*) * ε = 1 := omega_mul_epsilon

#eval myHyper
