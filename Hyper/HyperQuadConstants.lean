/-
  Combining both extensions: algebraic coefficients *and* π/e as formal
  generators, together.
  =======================================================================

  Two independent extensions of `HyperList.lean` exist so far:
    • `Hyper/HyperConstants.lean` — coefficients stay in `ℚ`, but π and e
      get their own formal exponent tracks alongside ε (multivariate
      exponents).
    • `Hyper/HyperQuadField.lean` — the exponent stays single (`ε`), but
      the coefficient field itself moves from `ℚ` to `Quad d = ℚ(√d)`
      (real algebraic numbers).

  These compose without conflict, because they act on two different slots
  of a term (coefficient vs. exponent) that never interact. This file does
  both at once: `Quad d`-valued coefficients, with three independent
  exponent tracks (ε, π, e).

  ⚠️ What this does *not* and *cannot* do: make `Quad d` itself contain π or
  e. `Quad d` is an *algebraic* extension of ℚ (`√d` is a root of `x² - d`);
  π and e are transcendental by definition, so no algebraic extension —
  extending `d`, or anything else about `Quad` — can ever reach them. That
  isn't a missing feature, it's the same transcendence fact from
  `Hyper/QuadField.lean`'s header. π/e can only enter as *exponent*
  generators (as here), never as `Quad`-field elements.
-/
import Hyper.QuadField

/-- A term with a `Quad d`-valued coefficient and three independent formal
    exponent tracks `(εExp, πExp, eExp)`. -/
abbrev QCTerm (d : ℤ) := Quad d × ℚ × ℚ × ℚ

/-- Hyperreal numbers over `ℚ(√d)`, with ε, π, e as independent generators. -/
abbrev QCHyper (d : ℤ) : Type := List (QCTerm d)

namespace QCHyper

variable {d : ℤ}

def mergeAdjacent : List (QCTerm d) → List (QCTerm d)
  | [] => []
  | [x] => [x]
  | (r₁, x₁) :: (r₂, x₂) :: rest =>
      if x₁ = x₂ then mergeAdjacent ((r₁ + r₂, x₁) :: rest)
      else (r₁, x₁) :: mergeAdjacent ((r₂, x₂) :: rest)
termination_by l => l.length
decreasing_by all_goals (simp_all; try omega)

def myle (p q : QCTerm d) : Bool := decide (q.2 ≤ p.2)

def simplify (a : QCHyper d) : QCHyper d :=
  (mergeAdjacent (a.mergeSort myle)) |>.filter (fun p => p.1 ≠ 0)

def merge (x y : QCHyper d) : QCHyper d :=
  if x = [] then y else if y = [] then x else simplify (x ++ y)

instance : Zero (QCHyper d) := ⟨([] : QCHyper d)⟩
instance : One (QCHyper d) := ⟨[(1, 0, 0, 0)]⟩
instance : Add (QCHyper d) := ⟨merge⟩
instance : Neg (QCHyper d) := ⟨fun x => x.map (fun (r, e) => (-r, e))⟩
instance : Sub (QCHyper d) := ⟨fun x y => x + -y⟩

/-- Multiplication: `Quad d` coefficients multiply as in `QuadField.lean`
    (so `√d · √d` collapses to the rational `d`); the three exponent tracks
    add independently, exactly as in `HyperConstants.lean` — neither
    mechanism interferes with the other. -/
instance : Mul (QCHyper d) := ⟨fun x y =>
  simplify ((x.product y).map (fun ((r1, e1), (r2, e2)) =>
    (r1 * r2, e1.1 + e2.1, e1.2.1 + e2.2.1, e1.2.2 + e2.2.2)))⟩

def epsilon : QCHyper d := [(1, 1, 0, 0)]
def omega : QCHyper d := [(1, -1, 0, 0)]
def piGen : QCHyper d := [(1, 0, 1, 0)]
def eGen : QCHyper d := [(1, 0, 0, 1)]
/-- `√d`, embedded as a coefficient — see the file header for why this is
    the only way an algebraic irrational like `√d` can appear here, and why
    π/e (transcendental) can't follow the same route. -/
def sqrtCoeff : QCHyper d := [(Quad.sqrtGen, 0, 0, 0)]

instance : Repr (QCHyper d) := inferInstanceAs (Repr (List (QCTerm d)))

-- ═══════════════════════════════════════════════════════════════════════════
-- Both mechanisms at once, checked exactly.
-- ═══════════════════════════════════════════════════════════════════════════

example : (epsilon * omega : QCHyper 2) = 1 := by native_decide
example : (sqrtCoeff * sqrtCoeff : QCHyper 2) = ([(2, 0, 0, 0)] : QCHyper 2) := by native_decide
example : (piGen * eGen : QCHyper 2) ≠ (piGen : QCHyper 2) := by native_decide

-- (√2·π)² = 2·π² — the algebraic coefficient squares away cleanly to a
-- rational, while the transcendental exponent track just doubles, with no
-- cross-collapse between the two mechanisms.
example : (sqrtCoeff * piGen : QCHyper 2) * (sqrtCoeff * piGen)
    = ([(2, 0, 2, 0)] : QCHyper 2) := by native_decide

-- (ε + π)² still expands to three genuinely distinct terms even with
-- `Quad d`-valued coefficients in play.
example : (epsilon + piGen : QCHyper 2) * (epsilon + piGen)
    = ([(1, 2, 0, 0), (2, 1, 1, 0), (1, 0, 2, 0)] : QCHyper 2) := by native_decide

end QCHyper
