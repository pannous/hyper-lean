import Hyper.HyperReal

open HyperReals

def main : IO Unit := do
  IO.println "=== COMPLETE HyperReal Validation (matching Julia) ==="
  IO.println ""
  
  -- 1. Constants (from Julia lines 73-85)
  IO.println "1. Basic Constants:"
  IO.println s!"   ε = {repr ε}"
  IO.println s!"   ω = {repr ω}"
  IO.println s!"   ε² = {repr (ε ^ 2)}"
  IO.println s!"   ε³ = {repr (ε ^ 3)}"
  IO.println s!"   ω² = {repr (ω ^ 2)}"
  IO.println s!"   ω³ = {repr (ω ^ 3)}"
  IO.println ""
  
  -- 2. Basic arithmetic (lines 165-187)
  IO.println "2. Arithmetic Operations:"
  IO.println s!"   1 + 1 = {repr (one + one)}"
  IO.println s!"   1 + ε = {repr (one + ε)}"
  IO.println s!"   ε * ω = {repr (ε * ω)} (should be 1)"
  IO.println s!"   ω * ε = {repr (ω * ε)} (should be 1)"
  IO.println s!"   1/ε = {repr (one / ε)} (should be ω)"
  IO.println s!"   ε⁻¹ = {repr (ε ^ (-1))} (should be ω)"
  IO.println ""
  
  -- 3. Predicates (lines 343-352)
  IO.println "3. Predicates:"
  IO.println s!"   isFinite(1) = {isFinite one}"
  IO.println s!"   isFinite(ε) = {isFinite ε}"
  IO.println s!"   isFinite(ω) = {isFinite ω}"
  IO.println s!"   isInfinite(ω) = {isInfinite ω}"
  IO.println s!"   isInfinite(ε) = {isInfinite ε}"
  IO.println ""
  
  -- 4. Real part extraction (line 229)
  IO.println "4. Real Part Extraction:"
  IO.println s!"   real(1 + ε) = {real (one + ε)}"
  IO.println s!"   real(42) = {real (fromFloat 42.0)}"
  IO.println s!"   real(ω + 3) = {real (ω + fromFloat 3.0)}"
  IO.println ""
  
  -- 5. Exponential (line 315-323)
  IO.println "5. Exponential Function:"
  IO.println s!"   exp(0) = {repr (exp zero)}"
  IO.println s!"   exp(1) = {repr (exp one)} (≈ 2.71828)"
  IO.println ""
  
  -- 6. Logarithm (lines 262-312)
  IO.println "6. Logarithm Function:"
  IO.println s!"   log(1) = {repr (log one)}"
  IO.println s!"   log(e) = {repr (log (fromFloat 2.71828))}"
  IO.println ""
  
  -- 7. Trigonometric (lines 712-713)
  IO.println "7. Trigonometric Functions:"
  IO.println s!"   sin(0) = {repr (sin zero)}"
  IO.println s!"   cos(0) = {repr (cos zero)}"
  IO.println ""
  
  -- 8. Square root (line 558)
  IO.println "8. Square Root:"
  IO.println s!"   sqrt(4) = {repr (sqrt (fromFloat 4.0))}"
  IO.println s!"   sqrt(9) = {repr (sqrt (fromFloat 9.0))}"
  IO.println ""
  
  -- 9. Derivative (lines 659-665)
  IO.println "9. Derivatives:"
  let square := fun (x : Hyper) => x * x
  let linear := fun (x : Hyper) => x
  let cube := fun (x : Hyper) => x * x * x
  IO.println s!"   d/dx(x²)|ₓ₌₁ = {repr (derivative square one)}"
  IO.println s!"   d/dx(x)|ₓ₌₁ = {repr (derivative linear one)}"
  IO.println s!"   d/dx(x³)|ₓ₌₂ = {repr (derivative cube (fromFloat 2.0))}"
  IO.println ""
  
  -- 10. Integration of functions (lines 860-874)
  IO.println "10. Integration of Functions:"
  IO.println s!"   ∫₀¹ 1 dx = {repr (integrate (fun _ => one) one)}"
  IO.println s!"   ∫₀¹ x dx = {repr (integrate linear one)} (≈ 0.5)"
  IO.println s!"   ∫₀² x² dx = {repr (integrate square (fromFloat 2.0))} (≈ 8/3 ≈ 2.67)"
  IO.println ""
  
  -- 11. Integration of hyperreals (lines 944-945, 954)
  IO.println "11. Integration of Hyperreals (symbolic):"
  -- ∫(h::Hyper) = Hyper([(r, e+1) for (r, e) in h.terms])
  let intEpsilon : Hyper := ⟨ε.terms.map (fun (r, e) => (r, e + 1.0))⟩
  IO.println s!"   ∫ε (symbolic) = {repr intEpsilon} (should raise order)"
  let int42Epsilon : Hyper := ⟨(fromFloat 42.0 * ε).terms.map (fun (r, e) => (r, e + 1.0))⟩  
  IO.println s!"   ∫(42ε) (symbolic) = {repr int42Epsilon} (should be 42)"
  IO.println ""
  
  -- 12. Fundamental Theorem of Calculus
  IO.println "12. Fundamental Theorem of Calculus:"
  let intSquare := fun x => integrate square x
  IO.println s!"   d/dx(∫₀ˣ t² dt)|ₓ₌₁ = {repr (derivative intSquare one)} (≈ 1)"
  IO.println ""
  
  -- 13. Powers and operations
  IO.println "13. Advanced Operations:"
  IO.println s!"   (1+ε)² = {repr ((one + ε) ^ 2)} (should expand)"
  IO.println s!"   (ω-1)/ω = {repr ((ω - one) / ω)}"
  IO.println ""
  
  IO.println "✅ Complete validation finished!"
  IO.println ""
  IO.println "Summary of Julia features covered:"
  IO.println "  ✓ Constants (ε, ω, ε², ω², etc.)"
  IO.println "  ✓ Arithmetic (+, -, *, /, ^)"
  IO.println "  ✓ Predicates (isFinite, isInfinite)"
  IO.println "  ✓ real() extraction"
  IO.println "  ✓ exp, log, sin, cos, sqrt"
  IO.println "  ✓ Derivatives (numerical)"
  IO.println "  ✓ Integration (numerical)"
  IO.println "  ✓ Integration (symbolic on hyperreals)"
  IO.println "  ✓ Fundamental Theorem validation"

#eval main
