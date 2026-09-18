/-
  Executable checks for `Hyper/HyperIntegral.lean`.

  Every claim of `notes/integral/integral-probability-foundations.md` that the
  implementation is supposed to deliver is evaluated here, exactly, in `R*`.
  Run with `lake env lean Hyper/probes/IntegralExamples.lean`.
-/
import Hyper.HyperIntegral

namespace Hypers
namespace HyperLists
namespace Integral

/-- Values print normalized, so `#eval` output is comparable. -/
def show' (x : R*) : R* := normalize x

-- ═══════════════════════════════════════════════════════════════════════════
-- The gauge, and the integral of the constant 1
-- ═══════════════════════════════════════════════════════════════════════════

/-- `∫_[0,1) 1 dx = ω·ε = 1` exactly: interval probabilities are untouched. -/
example : normalize (integral (constant 1) 0 1) = normalize 1 := by native_decide

/-- `∫_[0,L) 1 dx = L`. -/
example : normalize (integral (constant 1) 0 5) = normalize 5 := by native_decide

/-- Default domain, the reals: `∫_ℝ 1 dx = 2ω`, the README's `∫1 = 2ω`. -/
example : normalize (integralLine (constant 1)) = normalize (2 * omega) := by native_decide

/-- One-sided: `ƒ1 = ω` over `[0, ω)`. -/
example : normalize (integral (constant 1) 0 omega) = normalize omega := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- The point: P(X = y) = ε, the answer the framework exists for
-- ═══════════════════════════════════════════════════════════════════════════

/-- A single dot carries `ε` of a uniform law on `[0,1)`. -/
example : normalize (integral (constant 1) 0 epsilon) = normalize epsilon := by native_decide

/-- `P({y}) = p(y)·ε = ε`, via the density value rather than the interval. -/
example : normalize (uniformUnit.probPoint (1/2)) = normalize epsilon := by native_decide

/-- The uniform law on `[0,1)` really is a probability density. -/
example : uniformUnit.IsDensity := by native_decide

/-- `r` points carry `r·ε`. -/
example : normalize (integral (constant 1) 0 (3 * epsilon)) = normalize (3 * epsilon) := by
  native_decide

/-- Ordinary intervals are unharmed: `P([1/4, 3/4)) = 1/2`. -/
example : normalize (uniformUnit.prob (1/4) (3/4)) = normalize (1/2 : R*) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Uniform on the whole line: a point is second-order rare
-- ═══════════════════════════════════════════════════════════════════════════

/-- Normalization forces the infinitesimal density `ε/2` — and it works. -/
example : uniformLine.IsDensity := by native_decide

/-- `P({y}) = ε²/2` on the line, against `ε` on the unit interval. -/
example : normalize (uniformLine.probPoint 0) = normalize (scale (1/2) (epsilon * epsilon)) := by
  native_decide

/-- A whole finite interval of the line still gets only an infinitesimal. -/
example : normalize (uniformLine.prob 0 1) = normalize (scale (1/2) epsilon) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Atoms and the Dirac delta: ∫(−ε,ε)ω = 2 and ∫(0,ε)ω = 1 are consistent
-- ═══════════════════════════════════════════════════════════════════════════

/-- `ω` over the stencil `[-ε, ε)` — two dots — integrates to `2`. -/
example : normalize (integral (constant omega) (-epsilon) epsilon) = normalize 2 := by
  native_decide

/-- `ω` over one dot `[0, ε)` integrates to `1`: the same rule, half the stencil. -/
example : normalize (integral (constant omega) 0 epsilon) = normalize 1 := by native_decide

/-- Hence `∫δ = 1` exactly, for the unit spike on a point's cell. -/
example : normalize (integralLine (dirac 0)) = normalize 1 := by native_decide

/-- Half the stencil collects half of the *constant* `ω` — the README's
    "left-dirac"/"right-dirac" are statements about `ω`, not about `δ`. -/
example : normalize (integral (constant omega) (-epsilon) 0) = normalize 1 := by native_decide

/-- A spike outside the region contributes nothing. -/
example : normalize (integral (dirac 5) 0 1) = normalize 0 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- A mixed law needs no case split: atom plus continuous part in one density
-- ═══════════════════════════════════════════════════════════════════════════

/-- Mass `1/2` as an atom at the point `0`, mass `1/2` spread uniformly over
    `[0,1)` — one density, no case split. -/
def halfAtom : Distribution :=
  { density := { poly := [scale (1/2) 1], spikes := [{ position := 0, mass := 1/2 }] },
    low := 0, high := 1 }

example : halfAtom.IsDensity := by native_decide

/-- The atom returns its whole mass at the point, plus the continuous part's
    infinitesimal: `P({0}) = 1/2 + ε/2`. -/
example : normalize (halfAtom.probPoint 0) = normalize (1/2 + scale (1/2) epsilon) := by
  native_decide

/-- An ordinary point of the same law is only worth `ε/2`, so the atom is
    infinitely more likely — their ratio is of order `ω`. -/
example : normalize (halfAtom.probPoint (1/2)) = normalize (scale (1/2) epsilon) := by
  native_decide

/-- The distribution function jumps by exactly the atom's mass across the dot
    at `0`, with no point-weight bookkeeping. -/
example : normalize (halfAtom.prob 0 epsilon) = normalize (1/2 + scale (1/2) epsilon) := by
  native_decide

/-- The atom and the Dirac delta are the *same object*: `ω` unifies them, and
    `dirac` is definitionally the unit atom. -/
example : dirac 0 = atom 0 1 := rfl

example : normalize (integralLine (atom 0 1)) = normalize 1 := by native_decide

example : normalize ((atom 0 1).value 0) = normalize omega := by native_decide

/-- A point carries the whole atom, which is what `P({y}) = p(y)·ε` demands. -/
example : normalize (integral (atom 0 1) 0 epsilon) = normalize 1 := by native_decide

/-- The central difference quotient of a step returns something else: `ω/2` on
    each of the two halo cells, because its stencil is `2ε` wide.  Same mass,
    and every halo-aligned integral agrees with `δ` — -/
example : normalize (integralLine (stepDerivative 0)) = normalize 1 := by native_decide

example : normalize (integral (stepDerivative 0) (-epsilon) epsilon)
        = normalize (integral (dirac 0) (-epsilon) epsilon) := by native_decide

example : normalize (integral (stepDerivative 0) (-1) 1)
        = normalize (integral (dirac 0) (-1) 1) := by native_decide

/-- — and they come apart only on a *half*-halo, i.e. below the resolution the
    theory claims to describe: one cell sees all of `δ` but half the stencil. -/
example : normalize (integral (stepDerivative 0) 0 epsilon) = normalize (1/2 : R*) := by
  native_decide

example : normalize (integral (dirac 0) 0 epsilon) = normalize 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Moments, and the visible cost of the sampling convention
-- ═══════════════════════════════════════════════════════════════════════════

/-- Symmetric (midpoint) sampling: `E[X] = 1/2` exactly, no ε-bias. -/
example : normalize (integralWith midRule { poly := [0, 1] } 0 1) = normalize (1/2 : R*) := by
  native_decide

/-- Left-endpoint sampling: `E[X] = 1/2 − ε/2`, the bias of the convention. -/
example : normalize (integralWith leftRule { poly := [0, 1] } 0 1)
        = normalize (1/2 - scale (1/2) epsilon) := by native_decide

/-- Right-endpoint sampling: the bias flips sign. -/
example : normalize (integralWith rightRule { poly := [0, 1] } 0 1)
        = normalize (1/2 + scale (1/2) epsilon) := by native_decide

/-- Right minus left is exactly `ε·(f(b) − f(a))`. -/
example : normalize (integralWith rightRule { poly := [0, 1] } 0 1
                     - integralWith leftRule { poly := [0, 1] } 0 1) = normalize epsilon := by
  native_decide

/-- Second moment, midpoint rule: `1/3 − ε²/12`. -/
example : normalize (integralWith midRule { poly := [0, 0, 1] } 0 1)
        = normalize (1/3 - scale (1/12) (epsilon * epsilon)) := by native_decide

/-- Second moment, left rule: `1/3 − ε/2 + ε²/6`, as in the exercises. -/
example : normalize (integralWith leftRule { poly := [0, 0, 1] } 0 1)
        = normalize (1/3 - scale (1/2) epsilon + scale (1/6) (epsilon * epsilon)) := by
  native_decide

/-- Cubes still come out exactly, so the power-sum recursion is not a table of
    special cases: `∫_[0,1) x³ = 1/4 − ε²/8` under midpoint sampling. -/
example : normalize (integralWith midRule { poly := [0, 0, 0, 1] } 0 1)
        = normalize (1/4 - scale (1/8) (epsilon * epsilon)) := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Densities other than the uniform one
-- ═══════════════════════════════════════════════════════════════════════════

/-- The triangular density `2x` on `[0,1)` is exactly normalized under the
    symmetric convention. -/
def triangular : Distribution := { density := { poly := [0, 2] }, low := 0, high := 1 }

example : triangular.IsDensity := by native_decide

/-- `P({y}) = p(y)·ε = 2y·ε`: point probabilities follow the density. -/
example : normalize (triangular.probPoint (1/4)) = normalize (scale (1/2) epsilon) := by
  native_decide

/-- Uniform on `[0,4)`: density `1/4`, points worth `ε/4`. -/
example : (uniformOn 0 4).IsDensity := by native_decide

example : normalize ((uniformOn 0 4).probPoint 2) = normalize (scale (1/4) epsilon) := by
  native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Printed values, for reading rather than checking
-- ═══════════════════════════════════════════════════════════════════════════

#eval show' (integralLine (constant 1))                            -- 2ω
#eval show' (uniformUnit.probPoint 0)                              -- ε
#eval show' (uniformLine.probPoint 0)                              -- ε²/2
#eval show' (integralLine (dirac 0))                               -- 1
#eval show' (integralWith leftRule { poly := [0, 1] } 0 1)         -- 1/2 − ε/2
#eval show' (integralWith midRule { poly := [0, 1] } 0 1)          -- 1/2

end Integral
end HyperLists
end Hypers
