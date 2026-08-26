-- "ACTUAL" validation — real pass/fail checks, not just prints. Updated to
-- the current `R*` model; see validate.lean's header for why `log`/`sqrt`/
-- Riemann-`∫` are dropped (they were bare `sorry`s in the original) and how
-- `derivative` is reimplemented exactly via `ε⁻¹ = ω`.
import Hyper.HyperTranscendental

open Hypers
open Hypers.HyperLists

def derivative (f : R* → R*) (x : R*) : R* := (f (x + ε) - f (x - ε)) * ω * embedQ (1 / 2)

def checkEq (name : String) (actual expected : R*) : IO Unit := do
  if actual = expected then
    IO.println s!"✓ {name}"
  else
    IO.println s!"✗ {name}"
    IO.println s!"  Expected: {repr expected}"
    IO.println s!"  Got:      {repr actual}"

def checkBool (name : String) (actual expected : Bool) : IO Unit := do
  if actual == expected then
    IO.println s!"✓ {name}: {actual}"
  else
    IO.println s!"✗ {name}: got {actual}, expected {expected}"

def main : IO Unit := do
  IO.println "=== ACTUAL VALIDATION WITH CHECKS ==="
  IO.println ""

  IO.println "1. Basic Arithmetic Identities:"
  checkEq "ε * ω = 1" (ε * ω) 1
  checkEq "ω * ε = 1" (ω * ε) 1
  checkEq "1/ε = ω" (1 / ε) (ω)
  checkEq "ε⁻¹ = ω" (ε⁻¹) (ω)
  checkEq "ε² correct" (ε * ε) (embedQ 1 * ε * ε)
  checkEq "ω² correct" (ω * ω) (embedQ 1 * ω * ω)
  IO.println ""

  IO.println "2. Predicates:"
  checkBool "isFinite(1)" (isFinite (1 : R*)) true
  checkBool "isFinite(ε)" (isFinite (ε : R*)) true
  checkBool "isFinite(ω)" (isFinite (ω : R*)) false
  checkBool "isInfinite(ω)" (isInfinite (ω : R*)) true
  checkBool "isInfinite(ε)" (isInfinite (ε : R*)) false
  IO.println ""

  IO.println "3. Standard-Part Extraction (`st`, the old `real`):"
  checkEq "st(1 + ε)" (st (1 + ε : R*)) 1
  checkEq "st(42)" (st (42 : R*)) 42
  checkEq "st(ω + 3)" (st (ω + 3 : R*)) 3
  IO.println ""

  IO.println "4. Exponential (exact-ℚ Taylor series):"
  checkEq "exp(0)" (hexp 0) 1
  checkEq "exp(1) has standard part ≈ e" (st (hexp 1)) (embedQ (9864101 / 3628800))
  IO.println ""

  IO.println "5-6. Logarithm / square root: not ported — bare `sorry`s in the original."
  IO.println ""

  IO.println "7. Derivatives (exact, not tolerance-checked — CRITICAL TEST):"
  let square := fun (x : R*) => x * x
  let linear := fun (x : R*) => x
  checkEq "d/dx(x²)|ₓ₌₁" (derivative square 1) 2
  checkEq "d/dx(x)|ₓ₌₁" (derivative linear 1) 1
  -- Central difference on a cubic leaves a genuine `+ ε²` remainder (exactly
  -- `3x² + ε²`, not an approximation artifact) — hyper.jl's own equivalent
  -- assertion uses `~` (near), not `==`, for the same reason. Check the
  -- standard part instead of exact equality.
  checkEq "st(d/dx(x³)|ₓ₌₂)" (st (derivative (fun x => x * x * x) (embedQ 2))) (embedQ 12)
  IO.println ""

  IO.println "8. Integration: not ported (Riemann-sum operator over functions"
  IO.println "   is still missing from Hyper/ — see Hyper/probes/HyperExamples.lean)."
  IO.println ""

  IO.println "9. Symbolic Integration of Hyperreals — this one's exact `hint`:"
  checkEq "∫ε = 1" (hint ε) 1
  checkEq "∫(42ε) = 42" (hint (embedQ 42 * ε)) (embedQ 42)
  IO.println ""

  IO.println "10. Advanced Operations:"
  checkEq "(1+ε)² expands correctly" ((1 + ε) * (1 + ε)) (1 + embedQ 2 * ε + ε * ε)
  IO.println ""

  IO.println "11. Fundamental Theorem of Calculus: not ported — depends on the"
  IO.println "    missing Riemann-sum ∫ from item 8."
  IO.println ""

  IO.println "=== VALIDATION COMPLETE ==="

#eval main
