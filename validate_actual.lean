import Hyper.HyperReal

open HyperReals

-- Helper to check equality
def hyperEq (x y : Hyper) : Bool :=
  (simplify x).terms == (simplify y).terms

def checkEq (name : String) (actual : Hyper) (expected : Hyper) : IO Unit := do
  if hyperEq actual expected then
    IO.println s!"✓ {name}"
  else
    IO.println s!"✗ {name}"
    IO.println s!"  Expected: {repr expected}"
    IO.println s!"  Got:      {repr actual}"

def checkFloat (name : String) (actual : Float) (expected : Float) (tolerance : Float := 0.001) : IO Unit := do
  if (actual - expected).abs < tolerance then
    IO.println s!"✓ {name}: {actual} ≈ {expected}"
  else
    IO.println s!"✗ {name}: {actual} ≠ {expected}"

def checkBool (name : String) (actual : Bool) (expected : Bool) : IO Unit := do
  if actual == expected then
    IO.println s!"✓ {name}: {actual}"
  else
    IO.println s!"✗ {name}: got {actual}, expected {expected}"

def main : IO Unit := do
  IO.println "=== ACTUAL VALIDATION WITH CHECKS ==="
  IO.println ""
  
  IO.println "1. Basic Arithmetic Identities:"
  checkEq "ε * ω = 1" (ε * ω) one
  checkEq "ω * ε = 1" (ω * ε) one
  checkEq "1/ε = ω" (one / ε) ω
  checkEq "ε⁻¹ = ω" (ε ^ (-1)) ω
  checkEq "ε² correct" (ε ^ 2) ⟨[(1.0, -2.0)]⟩
  checkEq "ω² correct" (ω ^ 2) ⟨[(1.0, 2.0)]⟩
  IO.println ""
  
  IO.println "2. Predicates:"
  checkBool "isFinite(1)" (isFinite one) true
  checkBool "isFinite(ε)" (isFinite ε) true
  checkBool "isFinite(ω)" (isFinite ω) false
  checkBool "isInfinite(ω)" (isInfinite ω) true
  checkBool "isInfinite(ε)" (isInfinite ε) false
  IO.println ""
  
  IO.println "3. Real Part Extraction:"
  checkFloat "real(1 + ε)" (real (one + ε)) 1.0
  checkFloat "real(42)" (real (fromFloat 42.0)) 42.0
  checkFloat "real(ω + 3)" (real (ω + fromFloat 3.0)) 3.0
  IO.println ""
  
  IO.println "4. Exponential:"
  checkFloat "exp(0)" (real (exp zero)) 1.0
  checkFloat "exp(1)" (real (exp one)) 2.71828 0.00001
  IO.println ""
  
  IO.println "5. Logarithm:"
  checkFloat "log(1)" (real (log one)) 0.0 0.001
  checkFloat "log(e)" (real (log (fromFloat 2.71828))) 1.0 0.001
  IO.println ""
  
  IO.println "6. Square Root:"
  checkFloat "sqrt(4)" (real (sqrt (fromFloat 4.0))) 2.0 0.001
  checkFloat "sqrt(9)" (real (sqrt (fromFloat 9.0))) 3.0 0.001
  IO.println ""
  
  IO.println "7. Derivatives (CRITICAL TEST):"
  let square := fun (x : Hyper) => x * x
  let linear := fun (x : Hyper) => x
  checkFloat "d/dx(x²)|ₓ₌₁" (real (derivative square one)) 2.0 0.001
  checkFloat "d/dx(x)|ₓ₌₁" (real (derivative linear one)) 1.0 0.001
  checkFloat "d/dx(x³)|ₓ₌₂" (real (derivative (fun x => x*x*x) (fromFloat 2.0))) 12.0 0.01
  IO.println ""
  
  IO.println "8. Integration:"
  checkFloat "∫₀¹ 1 dx" (real (integrate (fun _ => one) one)) 1.0 0.01
  checkFloat "∫₀¹ x dx" (real (integrate linear one)) 0.5 0.01
  -- ∫₀² x² dx = [x³/3]₀² = 8/3 ≈ 2.6667
  checkFloat "∫₀² x² dx" (real (integrate square (fromFloat 2.0))) 2.6667 0.01
  IO.println ""
  
  IO.println "9. Symbolic Integration of Hyperreals:"
  -- ∫ε should raise order: ε has order -1, ∫ε should have order 0 (be real)
  let intEps := simplify ⟨ε.terms.map (fun (r, e) => (r, e + 1.0))⟩
  checkEq "∫ε = 1" intEps one
  -- ∫(42ε) = 42 (Julia line 954)
  let int42Eps := simplify ⟨(fromFloat 42.0 * ε).terms.map (fun (r, e) => (r, e + 1.0))⟩
  checkFloat "∫(42ε) = 42" (real int42Eps) 42.0 0.01
  IO.println ""
  
  IO.println "10. Advanced Operations:"
  -- (1+ε)² = 1 + 2ε + ε²
  let expanded := (one + ε) ^ 2
  let expected := one + fromFloat 2.0 * ε + ε^2
  checkEq "(1+ε)² expands correctly" expanded expected
  IO.println ""
  
  IO.println "11. Fundamental Theorem of Calculus:"
  -- d/dx(∫₀ˣ t² dt)|ₓ₌₁ should ≈ 1² = 1
  let intSquare := fun x => integrate square x
  let ftc_result := real (derivative intSquare one)
  checkFloat "FTC: d/dx(∫ₓ²)" ftc_result 1.0 0.01
  IO.println ""
  
  IO.println "=== VALIDATION COMPLETE ==="

#eval! main
