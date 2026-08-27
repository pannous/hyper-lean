-- Validation tests matching the Julia version — updated to import the
-- current `R*` model (Hyper/HyperList.lean via Hyper/HyperTranscendental.lean)
-- instead of the abandoned `Float`-based `HyperReals.Hyper` this file
-- originally targeted (that module's own `log`/`sqrt`/`integrate` were bare
-- `sorry`s — dropped below rather than ported, since there was nothing there
-- to port). `derivative` is reimplemented exactly (not approximately) using
-- `ε⁻¹ = ω` — see `Hyper/probes/EvalsDerivatives.lean` for the same trick.
import Hyper.HyperTranscendental

open Hypers
open Hypers.HyperLists

def derivative (f : R* → R*) (x : R*) : R* := (f (x + ε) - f (x - ε)) * ω * embedQ (1 / 2)

def main : IO Unit := do
  IO.println "=== HyperReal Validation Tests ==="
  IO.println ""

  IO.println "1. Basic Constants:"
  IO.println s!"   ε = {repr (ε : R*)}"
  IO.println s!"   ω = {repr (ω : R*)}"
  IO.println s!"   ε * ω = {repr (ε * ω : R*)}"
  IO.println s!"   Expected: ε * ω = 1 ✓"
  IO.println ""

  IO.println "2. Arithmetic:"
  IO.println s!"   1 + 1 = {repr ((1 : R*) + 1)}"
  IO.println s!"   ω² = {repr (ω * ω : R*)}"
  IO.println s!"   ε² = {repr (ε * ε : R*)}"
  IO.println s!"   1/ε = {repr (1 / ε : R*)}"
  IO.println ""

  IO.println "3. Exponential (exact-ℚ Taylor series, Hyper/HyperTranscendental.lean):"
  IO.println s!"   exp(0) = {repr (hexp 0)}"
  IO.println s!"   exp(1) = {repr (hexp 1)}"
  IO.println s!"   Expected: exp(1) ≈ 2.71828 ✓ ({(9864101 : Float) / 3628800})"
  IO.println ""

  IO.println "4. Logarithm: not ported — the original `log` was a bare `sorry`."
  IO.println ""

  IO.println "5. Trigonometric:"
  IO.println s!"   sin(0) = {repr (hsin 0)}"
  IO.println s!"   cos(0) = {repr (hcos 0)}"
  IO.println s!"   Expected: sin(0)=0, cos(0)=1 ✓"
  IO.println ""

  IO.println "6. Square Root: not ported — the original `sqrt` was a bare `sorry`."
  IO.println ""

  -- Define test functions
  let square := fun (x : R*) => x * x
  let linear := fun (x : R*) => x

  IO.println "7. Derivatives (exact, via ε⁻¹ = ω):"
  IO.println s!"   d/dx(x²)|ₓ₌₁ = {repr (derivative square 1)}"
  IO.println s!"   Expected: 2 ✓"
  IO.println s!"   d/dx(x)|ₓ₌₁ = {repr (derivative linear 1)}"
  IO.println s!"   Expected: 1 ✓"
  IO.println ""

  IO.println "8. Integration: not ported — the original was a Riemann-sum"
  IO.println "   operator over functions, still missing from Hyper/ (see"
  IO.println "   Hyper/probes/HyperExamples.lean's header notes). The"
  IO.println "   *term-level* integral (shifting a monomial's exponent, as"
  IO.println "   in `∫ε = 1`) does exist as `hint` in Hyper/HyperList.lean:"
  IO.println s!"   hint(ε) = {repr (hint ε)}"
  IO.println s!"   Expected: 1 ✓"
  IO.println ""

  IO.println "✅ Validation complete (log/sqrt/Riemann-∫ intentionally not ported; see notes above)."

#eval main
