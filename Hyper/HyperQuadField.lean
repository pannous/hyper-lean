/-
  Hyperreal numbers with an algebraic-number coefficient field.
  =================================================================

  `Hyper/HyperList.lean` builds `R* = List (𝔽 × 𝔽)` with `𝔽 := ℚ` playing
  both roles — the exponent (order of infinitesimal/infinite) *and* the
  coefficient (how much of that order). Here the two roles are split:
  exponents stay in `ℚ` (fractional orders like `ε^(1/2)` still make sense),
  but **coefficients move to `Quad d` — `ℚ(√d)`, a genuine field of real
  algebraic numbers** (`Hyper/QuadField.lean`). This is what "set the field
  𝔽 to a richer field" concretely means: `√2 · ε` is now a first-class
  value, not just `ε` with an approximated scalar bolted on afterward.

  Same `simplify`/`merge`/`Mul` recipe as `HyperList.lean`, coefficient type
  swapped. A new, standalone file — `HyperList.lean` (~1250 lines, proved
  order, a `Field R*` instance) is not touched, for the same reason
  `Hyper/HyperConstants.lean` wasn't merged into it either.
-/
import Hyper.QuadField

/-- A term `(coefficient, εExp)`, coefficient now in `Quad d` instead of `ℚ`. -/
abbrev QTerm (d : ℤ) := Quad d × ℚ

/-- Hyperreal numbers with `Quad d`-valued coefficients. -/
abbrev QHyper (d : ℤ) : Type := List (QTerm d)

namespace QHyper

variable {d : ℤ}

def mergeAdjacent : List (QTerm d) → List (QTerm d)
  | [] => []
  | [x] => [x]
  | (r₁, e₁) :: (r₂, e₂) :: rest =>
      if e₁ = e₂ then mergeAdjacent ((r₁ + r₂, e₁) :: rest)
      else (r₁, e₁) :: mergeAdjacent ((r₂, e₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

/-- Descending order by exponent, same convention as `HyperList.lean`'s `myle`. -/
def myle (p q : QTerm d) : Bool := decide (q.2 ≤ p.2)

def simplify (a : QHyper d) : QHyper d :=
  (mergeAdjacent (a.mergeSort myle)) |>.filter (fun p => p.1 ≠ 0)

def merge (x y : QHyper d) : QHyper d :=
  if x = [] then y else if y = [] then x else simplify (x ++ y)

instance : Zero (QHyper d) := ⟨([] : QHyper d)⟩
instance : One (QHyper d) := ⟨[(1, 0)]⟩
instance : Add (QHyper d) := ⟨merge⟩
instance : Neg (QHyper d) := ⟨fun x => x.map (fun (r, e) => (-r, e))⟩
instance : Sub (QHyper d) := ⟨fun x y => x + -y⟩

/-- Multiplication: cartesian product of terms, multiply coefficients **in
    `Quad d`** (so `√d · √d` collapses to the rational `d`, exactly),
    add exponents in `ℚ` as before. -/
instance : Mul (QHyper d) := ⟨fun x y =>
  simplify ((x.product y).map (fun ((r1, e1), (r2, e2)) => (r1 * r2, e1 + e2)))⟩

def epsilon : QHyper d := [(1, -1)]
def omega : QHyper d := [(1, 1)]

/-- `√d`, embedded as a coefficient — an irrational infinitesimal-free scalar. -/
def sqrtCoeff : QHyper d := [(Quad.sqrtGen, 0)]

instance : Repr (QHyper d) := inferInstanceAs (Repr (List (QTerm d)))

-- ═══════════════════════════════════════════════════════════════════════════
-- The actual point: irrational coefficients coexist with the ε/ω order
-- structure, and multiply exactly.
-- ═══════════════════════════════════════════════════════════════════════════

#eval (sqrtCoeff * epsilon : QHyper 2) -- √2 · ε, an infinitesimal with an irrational coefficient

example : (epsilon * omega : QHyper 2) = 1 := by native_decide
example : (sqrtCoeff * sqrtCoeff : QHyper 2) = ([(2, 0)] : QHyper 2) := by native_decide -- (√2)² = 2
example : (sqrtCoeff * epsilon * omega : QHyper 2) = sqrtCoeff := by native_decide -- √2·ε·ω = √2
example : (sqrtCoeff * epsilon) * (sqrtCoeff * epsilon)
    = ([((2 : Quad 2), -2)] : QHyper 2) := by native_decide -- (√2·ε)² = 2·ε²
example : (sqrtCoeff : QHyper 2) ≠ (0 : QHyper 2) := by native_decide
-- 2√2: doubling the coefficient, not the exponent.
example : (sqrtCoeff : QHyper 2) + sqrtCoeff = ([(⟨0, 2⟩, 0)] : QHyper 2) := by native_decide

end QHyper
