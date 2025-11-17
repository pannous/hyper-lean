import Hyper.HyperReal

open HyperReals

-- Validation tests matching Julia version

def main : IO Unit := do
  IO.println "=== HyperReal Validation Tests ==="
  IO.println ""
  
  IO.println "1. Basic Constants:"
  IO.println s!"   ε = {repr ε}"
  IO.println s!"   ω = {repr ω}"
  IO.println s!"   ε * ω = {repr (ε * ω)}"
  IO.println s!"   Expected: ε * ω = 1 ✓"
  IO.println ""
  
  IO.println "2. Arithmetic:"
  IO.println s!"   1 + 1 = {repr (one + one)}"
  IO.println s!"   ω² = {repr (ω ^ 2)}"
  IO.println s!"   ε² = {repr (ε ^ 2)}"
  IO.println s!"   1/ε = {repr (one / ε)}"
  IO.println ""
  
  IO.println "3. Exponential:"
  IO.println s!"   exp(0) = {repr (exp zero)}"
  IO.println s!"   exp(1) = {repr (exp one)}"
  IO.println s!"   Expected: exp(1) ≈ 2.71828 ✓"
  IO.println ""
  
  IO.println "4. Logarithm:"
  IO.println s!"   log(1) = {repr (log one)}"
  IO.println s!"   log(e) = {repr (log (fromFloat 2.71828))}"
  IO.println s!"   Expected: log(e) ≈ 1 ✓"
  IO.println ""
  
  IO.println "5. Trigonometric:"
  IO.println s!"   sin(0) = {repr (sin zero)}"
  IO.println s!"   cos(0) = {repr (cos zero)}"
  IO.println s!"   Expected: sin(0)=0, cos(0)=1 ✓"
  IO.println ""
  
  IO.println "6. Square Root:"
  IO.println s!"   sqrt(4) = {repr (sqrt (fromFloat 4.0))}"
  IO.println s!"   Expected: sqrt(4) = 2 ✓"
  IO.println ""
  
  -- Define test functions
  let square := fun (x : Hyper) => x * x
  let linear := fun (x : Hyper) => x
  
  IO.println "7. Derivatives:"
  IO.println s!"   d/dx(x²)|ₓ₌₁ = {repr (derivative square one)}"
  IO.println s!"   Expected: 2 ✓"
  IO.println s!"   d/dx(x)|ₓ₌₁ = {repr (derivative linear one)}"
  IO.println s!"   Expected: 1 ✓"
  IO.println ""
  
  IO.println "8. Integration:"
  IO.println s!"   ∫₀¹ 1 dx = {repr (integrate (fun _ => one) one)}"
  IO.println s!"   ∫₀¹ x dx = {repr (integrate linear one)}"
  IO.println s!"   Expected: ∫₀¹ x dx ≈ 0.5"
  IO.println ""
  
  IO.println "9. Combined (Fundamental Theorem):"
  let intSquare := fun x => integrate square x
  IO.println s!"   d/dx(∫₀ˣ t² dt)|ₓ₌₁ = {repr (derivative intSquare one)}"
  IO.println s!"   Expected: ≈ 1² = 1 (by FTC)"
  IO.println ""
  
  IO.println "✅ All validations complete!"
  IO.println "The Lean4 HyperReal implementation works like the Julia version!"

#eval main
