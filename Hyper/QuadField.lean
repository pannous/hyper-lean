/-
  ℚ(√d): a genuine, decidable, exact field of real algebraic numbers.
  =====================================================================

  The general field of real algebraic numbers — arbitrary-degree roots,
  represented canonically and compared exactly via root isolation (Sturm
  sequences) — is a serious undertaking (what Sage's `QQbar` or
  Mathematica's `Root` objects are); Mathlib has no ready computable
  instance for it (`AlgebraicClosure` is classical/noncomputable,
  `IsAlgebraic` is a bare `Prop`).

  A genuine, narrower instance *is* fully achievable: quadratic extensions
  `ℚ(√d)`, for a fixed non-square integer `d`. Elements are pairs `(a, b)`
  meaning `a + b·√d`. This really is a field of real algebraic numbers
  (`√d` is a root of `x² - d`), with fully exact, decidable arithmetic and
  order — no numeric approximation of `√d` is ever computed anywhere below;
  comparisons reduce to comparing `a²` against `d·b²` in `ℚ`, exactly.

  Used by `Hyper/HyperQuadField.lean` as `HyperList.lean`'s coefficient
  field, in place of plain `ℚ`.
-/
import Mathlib.Data.EReal.Basic
import Mathlib.Tactic.NormNum

/-- `a + b·√d`, for a fixed `d : ℤ`. A genuine field whenever `d` is not a
    perfect square (so `x² - d` has no rational root and the norm below is
    never an accidental zero divisor). -/
structure Quad (d : ℤ) where
  a : ℚ
  b : ℚ
deriving DecidableEq, Repr

namespace Quad

variable {d : ℤ}

instance : Zero (Quad d) := ⟨⟨0, 0⟩⟩
instance : One (Quad d) := ⟨⟨1, 0⟩⟩
instance {n : ℕ} : OfNat (Quad d) n := ⟨⟨n, 0⟩⟩

instance : Add (Quad d) := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩
instance : Neg (Quad d) := ⟨fun x => ⟨-x.a, -x.b⟩⟩
instance : Sub (Quad d) := ⟨fun x y => ⟨x.a - y.a, x.b - y.b⟩⟩
instance : Mul (Quad d) := ⟨fun x y => ⟨x.a * y.a + (d : ℚ) * x.b * y.b, x.a * y.b + x.b * y.a⟩⟩

/-- The field norm `a² - d·b²`. Nonzero for every `(a, b) ≠ (0, 0)` exactly
    when `d` isn't a perfect square (of a rational, hence of an integer) —
    that's what makes `Inv` below total and correct. -/
def norm (x : Quad d) : ℚ := x.a ^ 2 - (d : ℚ) * x.b ^ 2

instance : Inv (Quad d) := ⟨fun x => if x = 0 then 0 else ⟨x.a / x.norm, -x.b / x.norm⟩⟩
instance : Div (Quad d) := ⟨fun x y => x * y⁻¹⟩

/-- `√d` itself, as an element of `Quad d`. -/
def sqrtGen : Quad d := ⟨0, 1⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- Arithmetic sanity checks.
-- ═══════════════════════════════════════════════════════════════════════════

example : (sqrtGen : Quad 2) * sqrtGen = 2 := by native_decide
example : (sqrtGen : Quad 2)⁻¹ * sqrtGen = 1 := by native_decide
example : ((1 : Quad 2) + sqrtGen) * (1 - sqrtGen) = -1 := by native_decide
example : (sqrtGen : Quad 5) * sqrtGen = 5 := by native_decide

/-- The golden ratio `φ = (1+√5)/2`, satisfying `φ² = φ + 1` exactly. -/
def goldenRatio : Quad 5 := (1 : Quad 5) / 2 + sqrtGen / 2

example : goldenRatio * goldenRatio = goldenRatio + 1 := by native_decide

-- ═══════════════════════════════════════════════════════════════════════════
-- Order: same-sign (or one-zero) coefficients settle it directly; opposite
-- signs need comparing `a²` against `d·b²` exactly — never `√d` itself.
-- ═══════════════════════════════════════════════════════════════════════════

/-- `Ordering.gt`/`.lt`/`.eq` for `x` against `0`. -/
def cmp (x : Quad d) : Ordering :=
  if 0 ≤ x.a ∧ 0 ≤ x.b then (if x.a = 0 ∧ x.b = 0 then .eq else .gt)
  else if x.a ≤ 0 ∧ x.b ≤ 0 then .lt
  else if 0 < x.a then compare (x.a ^ 2) ((d : ℚ) * x.b ^ 2) -- here b < 0
  else compare ((d : ℚ) * x.b ^ 2) (x.a ^ 2) -- here a < 0, b > 0

instance : LT (Quad d) := ⟨fun x y => cmp (x - y) = .lt⟩
instance : LE (Quad d) := ⟨fun x y => cmp (x - y) ≠ .gt⟩
instance (x y : Quad d) : Decidable (x < y) := inferInstanceAs (Decidable (cmp (x - y) = .lt))
instance (x y : Quad d) : Decidable (x ≤ y) := inferInstanceAs (Decidable (cmp (x - y) ≠ .gt))

example : (1 : Quad 2) < sqrtGen := by native_decide -- 1 < √2
example : (sqrtGen : Quad 2) < 2 := by native_decide -- √2 < 2
example : (0 : Quad 2) < sqrtGen := by native_decide
example : -(sqrtGen : Quad 2) < -1 := by native_decide -- -√2 < -1
example : (1 : Quad 2) + sqrtGen > 2 := by native_decide -- 1+√2 > 2
example : (sqrtGen : Quad 5) < 3 := by native_decide -- √5 < 3
example : (2 : Quad 5) < sqrtGen := by native_decide -- 2 < √5
example : (1 : Quad 5) < goldenRatio := by native_decide
example : goldenRatio < (2 : Quad 5) := by native_decide

end Quad
